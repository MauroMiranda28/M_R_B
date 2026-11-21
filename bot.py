"""Survivor bot for mechfight/1: placement is everything, so stay in the zone, avoid needless fights,
punish whoever attacks us, keep our front armor toward threats, and heal whenever possible."""
import array
import gc
import heapq
import json
import math
import os
import random
import sys
import time
import zlib

import mechfight as mf

TAU = 2.0 * math.pi
HERE = os.path.dirname(os.path.abspath(__file__))
UNSET = -32768

UPGRADE_PRIORITY = [
    "armor", "plating", "nanites", "laser_damage", "gun_damage", "laser_charge", "gun_rate",
    "lightning_efficiency", "servos", "lightning_range", "capacitor", "reactor", "gyros",
    "gun_velocity", "gun_mag", "jets", "sensors", "lightning_chain", "laser_pierce",
    "mortar_reload", "mortar_velocity", "mortar_splash",
]
WANT_WEAPON = {"laser": 3, "lightning": 2}  # never take mortar: lasers cook it off


def wrap(a):
    return (a + math.pi) % TAU - math.pi


def log(*a):
    print(*a, file=sys.stderr, flush=True)


# ---------------------------------------------------------------------------------------- map
class Nav:
    def __init__(self, path):
        raw = zlib.decompress(open(path, "rb").read())
        nl = raw.index(b"\n")
        h = json.loads(raw[:nl])
        self.nx, self.ny = h["nx"], h["ny"]
        self.minx, self.miny, self.cell = h["minX"], h["minY"], h["cell"]
        n = self.nx * self.ny
        o = nl + 1
        self.blk = raw[o:o + n]
        o += n
        self.top = array.array("h")
        self.top.frombytes(raw[o:o + 2 * n])
        o += 2 * n
        self.base = array.array("h")
        self.base.frombytes(raw[o:o + 2 * n])
        o += 2 * n
        self.surf = array.array("h")
        self.surf.frombytes(raw[o:o + 2 * n])
        o += 2 * n
        self.otop = array.array("h")
        self.otop.frombytes(raw[o:o + 2 * n])
        if sys.byteorder != "little":
            for a in (self.top, self.base, self.surf, self.otop):
                a.byteswap()
        self.inv = 1.0 / self.cell
        # standing height per cell (m): roof/obstacle top on walls, surface elsewhere
        blk = self.blk
        self.stand = array.array("f", [(self.otop[c] if blk[c] == 2 else self.surf[c]) * 0.1 for c in range(n)])

    def stand_at(self, x, y):
        return self.stand[self.idx(x, y)]

    def idx(self, x, y):
        i = int((x - self.minx) * self.inv)
        j = int((y - self.miny) * self.inv)
        if i < 0:
            i = 0
        elif i >= self.nx:
            i = self.nx - 1
        if j < 0:
            j = 0
        elif j >= self.ny:
            j = self.ny - 1
        return j * self.nx + i

    def center(self, c):
        j, i = divmod(c, self.nx)
        return (self.minx + (i + 0.5) * self.cell, self.miny + (j + 0.5) * self.cell)

    def ground(self, x, y):
        return self.surf[self.idx(x, y)] * 0.1

    def wall(self, x, y):
        return self.blk[self.idx(x, y)] == 2

    def free(self, x, y):
        return self.blk[self.idx(x, y)] == 0

    def snap(self, x, y, maxr=14):
        c = self.idx(x, y)
        if self.blk[c] == 0:
            return c
        nx = self.nx
        ci, cj = c % nx, c // nx
        best, bd = None, 1e9
        for r in range(1, maxr + 1):
            for dj in range(-r, r + 1):
                for di in (-r, r) if abs(dj) != r else range(-r, r + 1):
                    i, j = ci + di, cj + dj
                    if 0 <= i < nx and 0 <= j < self.ny and self.blk[j * nx + i] == 0:
                        d = di * di + dj * dj
                        if d < bd:
                            bd, best = d, j * nx + i
            if best is not None:
                return best
        return None

    def walk_clear(self, ax, ay, bx, by, soft=2.5):
        """Straight walk from a to b avoids walls (and wall margins beyond `soft` m of a)."""
        dx, dy = bx - ax, by - ay
        d = math.hypot(dx, dy)
        if d < 0.5:
            return True
        n = int(d / 0.9) + 1
        blk, idx = self.blk, self.idx
        for k in range(1, n + 1):
            f = k / n
            v = blk[idx(ax + dx * f, ay + dy * f)]
            if v == 2 or (v == 1 and d * f > soft):
                return False
        return True

    def los(self, a, b, skip_end=2.0):
        """3D line of sight against buildings and terrain."""
        dx, dy, dz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
        d = math.sqrt(dx * dx + dy * dy + dz * dz)
        if d < 3.0:
            return True
        step = 1.5
        n = int(d / step)
        top, base, surf, idx = self.top, self.base, self.surf, self.idx
        k0 = 1
        kend = n - int(skip_end / step)
        for k in range(k0, kend + 1):
            f = k / n
            x, y, z = a[0] + dx * f, a[1] + dy * f, a[2] + dz * f
            c = idx(x, y)
            zz = z * 10.0
            t = top[c]
            if t != UNSET and base[c] - 5 <= zz <= t:
                return False
            if surf[c] > zz + 3:
                return False
        return True

    def cover_near(self, x, y, rad=10):
        """A free cell near (x, y) that touches a wall, if any (stand next to cover)."""
        c0 = self.idx(x, y)
        nx = self.nx
        ci, cj = c0 % nx, c0 // nx
        blk = self.blk
        best, bs = None, 1e9
        for dj in range(-rad, rad + 1, 1):
            for di in range(-rad, rad + 1, 1):
                i, j = ci + di, cj + dj
                if not (2 <= i < nx - 2 and 2 <= j < self.ny - 2):
                    continue
                c = j * nx + i
                if blk[c] != 0:
                    continue
                walls = 0
                for o in (2, -2, 2 * nx, -2 * nx, 2 + 2 * nx, 2 - 2 * nx, -2 + 2 * nx, -2 - 2 * nx):
                    if blk[c + o] == 2:
                        walls += 1
                if walls == 0:
                    continue
                s = math.hypot(di, dj) - 0.8 * min(walls, 3)
                if s < bs:
                    bs, best = s, c
        return self.center(best) if best is not None else None


class Planner:
    """Time-sliced weighted A* on the nav grid."""

    def __init__(self, nav):
        self.nav = nav
        nx = nav.nx
        s2 = math.sqrt(2.0)
        self.nbr = [(1, 1.0, 0, 0), (-1, 1.0, 0, 0), (nx, 1.0, 0, 0), (-nx, 1.0, 0, 0),
                    (1 + nx, s2, 1, nx), (1 - nx, s2, 1, -nx), (-1 + nx, s2, -1, nx), (-1 - nx, s2, -1, -nx)]
        self.active = False
        self.goal_xy = None
        self.result = None  # list of (x, y) or [] on failure

    def start(self, sx, sy, gx, gy):
        nav = self.nav
        s = nav.idx(sx, sy)
        g = nav.snap(gx, gy, 20)
        self.goal_xy = (gx, gy)
        self.result = None
        if s is None or g is None:
            self.active = False
            self.result = []
            return
        self.s, self.g = s, g
        self.gi, self.gj = g % nav.nx, g // nav.nx
        self.open = [(0.0, 0.0, s)]
        self.cost = {s: 0.0}
        self.par = {s: -1}
        self.exp = 0
        self.active = True

    def _h(self, c):
        nx = self.nav.nx
        di = abs(c % nx - self.gi)
        dj = abs(c // nx - self.gj)
        return 1.25 * (max(di, dj) + 0.414 * min(di, dj))

    def step(self, deadline):
        if not self.active:
            return
        blk = self.nav.blk
        stand = self.nav.stand
        last = len(blk) - self.nav.nx - 2
        open_, cost, par, nbr = self.open, self.cost, self.par, self.nbr
        g = self.g
        pop, push, h = heapq.heappop, heapq.heappush, self._h
        n = 0
        while open_:
            n += 1
            if (n & 63) == 0 and time.perf_counter() > deadline:
                return
            f, gc_, c = pop(open_)
            if c == g:
                self._finish(c)
                return
            if gc_ > cost.get(c, 1e18):
                continue
            self.exp += 1
            if self.exp > 90000:
                break
            if c <= self.nav.nx or c >= last:
                continue
            bc = blk[c]
            for o, w, ox, oy in nbr:
                d = c + o
                b = blk[d]
                if b == 2:
                    # crossing a wall / roof: jump-jet over it, priced by the climb
                    rise = stand[d] - stand[c]
                    if rise > 48.0:
                        continue
                    ng = gc_ + w * 5.0 + (rise * 1.5 if rise > 0 else 0.0)
                else:
                    if ox and bc != 2 and (blk[c + ox] == 2 or blk[c + oy] == 2):
                        continue
                    ng = gc_ + (w * 3.0 if b == 1 else w)
                if ng < cost.get(d, 1e18):
                    cost[d] = ng
                    par[d] = c
                    push(open_, (ng + h(d), ng, d))
        self.active = False
        self.result = []
        self.open = self.cost = self.par = None

    def _finish(self, c):
        cells = []
        par = self.par
        while c != -1:
            cells.append(c)
            c = par[c]
        cells.reverse()
        ctr = self.nav.center
        blk = self.nav.blk
        # keep every wall cell (climb points), thin out the open ones
        keep = [k for n_, k in enumerate(cells) if n_ % 2 == 0 or blk[k] == 2
                or (n_ + 1 < len(cells) and blk[cells[n_ + 1]] == 2)]
        self.result = [ctr(k) for k in keep] + [ctr(cells[-1])]
        self.active = False
        self.open = self.cost = self.par = None


# ---------------------------------------------------------------------------------------- bot
class Bot:
    name = "survivor-v1"

    def __init__(self, hello):
        cfg = hello["config"]
        self.cfg = cfg
        self.me = int(hello["slot"])
        self.rng = random.Random(int(hello.get("seed", 0)))
        self.nav = Nav(os.path.join(HERE, "nav.bin"))
        self.plan = Planner(self.nav)
        self.path = None
        self.path_goal = None
        self.path_i = 0
        self.path_t = -99.0
        self.reach = cfg["loot"]["pickup_radius"]
        self.cube_r = cfg["cubes"]["pickup_radius"]
        self.mech_cfg = cfg["mech"]
        self.w_cfg = cfg["weapons"]
        self.t = 0.0
        self.attackers = {}  # id -> (last time, damage in window)
        self.threat_bearing = None
        self.threat_t = -99.0
        self.strafe = 1.0
        self.strafe_t = 0.0
        self.hist = []  # (t, x, y)
        self.stuck_until = -1.0
        self.stuck_dir = None
        self.jet_until = -1.0
        self.bad_pickups = {}
        self.charging_since = {}
        self.last_target = None
        self.last_target_t = -99.0
        self.sound_look = None
        self.sound_look_t = -99.0
        self.cover = None
        self.cover_for = None
        self.state = ""
        self.slow_ticks = 0
        gc.collect()
        gc.freeze()

    # ------------------------------------------------------------------ helpers
    def zone_now(self, z, t):
        ss, se = z["shrink_start"], z["shrink_end"]
        if t <= ss or se <= ss:
            f = 0.0
        else:
            f = min(1.0, (t - ss) / (se - ss))
        c, n = z["center"], z["next_center"]
        return (c[0] + (n[0] - c[0]) * f, c[1] + (n[1] - c[1]) * f,
                z["radius"] + (z["next_radius"] - z["radius"]) * f)

    def in_circle(self, x, y, cx, cy, r, margin=0.0):
        return math.hypot(x - cx, y - cy) <= r - margin

    def safe_spot(self, z, x, y):
        """Where we want to stand: inside the next circle, on our side of it."""
        nc = z["next_center"]
        R = z["next_radius"]
        rr = max(0.0, min(R * 0.55, R - 10.0))
        d = math.hypot(x - nc[0], y - nc[1])
        if d <= rr:
            return (x, y), True
        if d < 1e-6:
            return (nc[0], nc[1]), False
        return (nc[0] + (x - nc[0]) / d * rr, nc[1] + (y - nc[1]) / d * rr), False

    def nav_move(self, x, y, gx, gy, budget_end):
        """Unit move vector toward goal following the planned path."""
        nav = self.nav
        dx, dy = gx - x, gy - y
        d = math.hypot(dx, dy)
        if d < 1.5:
            return 0.0, 0.0
        if d < 70 and nav.walk_clear(x, y, gx, gy):
            self.path = None
            return dx / d, dy / d
        # (re)plan?
        need = (self.path is None or self.path_goal is None
                or math.hypot(self.path_goal[0] - gx, self.path_goal[1] - gy) > 8.0
                or self.t - self.path_t > 12.0)
        if self.path and not need:
            px, py = self.path[min(self.path_i, len(self.path) - 1)]
            if math.hypot(px - x, py - y) > 14.0:
                need = True
        if need:
            if not self.plan.active or self.plan.goal_xy is None or \
                    math.hypot(self.plan.goal_xy[0] - gx, self.plan.goal_xy[1] - gy) > 8.0:
                self.plan.start(x, y, gx, gy)
            self.plan.step(budget_end)
            if not self.plan.active and self.plan.result is not None:
                res = self.plan.result
                self.plan.result = None
                self.path_t = self.t
                self.path_goal = self.plan.goal_xy
                if res:
                    self.path = res
                    self.path_i = 0
                else:
                    self.path = None
                    self.path_goal = (gx, gy)
        if not self.path:
            return dx / d, dy / d
        p = self.path
        while self.path_i < len(p) - 1 and math.hypot(p[self.path_i][0] - x, p[self.path_i][1] - y) < 3.0:
            self.path_i += 1
        tgt = p[self.path_i]
        for k in (24, 16, 10, 6, 3, 1):
            j = self.path_i + k
            if j >= len(p):
                j = len(p) - 1
            if j <= self.path_i:
                continue
            if nav.walk_clear(x, y, p[j][0], p[j][1]):
                tgt = p[j]
                break
        ex, ey = tgt[0] - x, tgt[1] - y
        e = math.hypot(ex, ey)
        if e < 1e-6:
            return dx / d, dy / d
        return ex / e, ey / e

    def climb_ctl(self, x, y, z, mx, my, grounded, energy, urgent):
        m = math.hypot(mx, my)
        if m < 0.3:
            return None
        ux, uy = mx / m, my / m
        nav = self.nav
        need = -1e9
        for dd in (2.8, 4.5):
            c = nav.idx(x + ux * dd, y + uy * dd)
            if nav.blk[c] == 2:
                need = max(need, nav.stand[c])
        if need < -1e8:
            return None
        here = nav.stand_at(x, y)
        if need - here < 1.2 and need - z < 1.2:
            return None  # no real obstacle
        rise = need - z
        if grounded:
            if rise <= 1.0 or rise > 56.0:
                return None
            need_e = min(98.0, rise * 1.75 + 8.0)
            if energy >= need_e or urgent:
                return "jump"
            return "wait"
        if rise > -1.5 and energy > 1.0:
            return "jet"
        return None

    def deflect(self, x, y, mx, my, look=5.0):
        """Rotate a combat move so it doesn't drive into a wall."""
        m = math.hypot(mx, my)
        if m < 1e-6:
            return mx, my
        ux, uy = mx / m, my / m
        for ang in (0.0, 0.5, -0.5, 1.0, -1.0, 1.6, -1.6, 2.4, -2.4):
            ca, sa = math.cos(ang), math.sin(ang)
            vx, vy = ux * ca - uy * sa, ux * sa + uy * ca
            if not self.nav.wall(x + vx * look, y + vy * look) and not self.nav.wall(x + vx * 2.5, y + vy * 2.5):
                if ang != 0.0 and abs(ang) >= 1.0:
                    self.strafe = -self.strafe
                return vx * m, vy * m
        return mx, my

    def lead(self, mx, my, mz, p, v, speed, airborne):
        px, py, pz = p
        vx, vy, vz = v
        tt = math.sqrt((px - mx) ** 2 + (py - my) ** 2 + (pz - mz) ** 2) / speed
        g = self.mech_cfg.get("gravity", 22.0)
        for _ in range(3):
            qx, qy, qz = px + vx * tt, py + vy * tt, pz + vz * tt
            if airborne:
                qz -= 0.5 * g * tt * tt
                qz = max(qz, self.nav.ground(qx, qy) + 0.5)
            tt = math.sqrt((qx - mx) ** 2 + (qy - my) ** 2 + (qz - mz) ** 2) / speed
        return qx, qy, qz

    def aim_to(self, mx, my, mz, q):
        dx, dy = q[0] - mx, q[1] - my
        hd = math.hypot(dx, dy)
        return math.atan2(dy, dx), math.atan2(q[2] - mz, max(hd, 0.1)), math.sqrt(hd * hd + (q[2] - mz) ** 2)

    # ------------------------------------------------------------------ main
    def act(self, obs):
        t0 = time.perf_counter()
        budget_end = t0 + 0.016
        self.t = t = obs["t"]
        me = obs["self"]
        x, y, z = me["pos"]
        vx, vy, vz = me["vel"]
        hp, mhp = me["hp"], max(1.0, me["max_hp"])
        hpf = hp / mhp
        energy = me["energy"]
        stats = me.get("stats", {})
        muzzle = z + stats.get("muzzle_height", 7.0)
        eye = z + stats.get("eye_height", 8.0)
        ayaw, apitch = me["aim"]
        nav = self.nav
        act = {"tick": obs["tick"]}

        # ---------- events
        for ev in obs.get("events", []):
            et = ev.get("type")
            if et == "damaged":
                by = ev.get("by")
                if by is not None and ev.get("weapon") != "zone":
                    last = self.attackers.get(by)
                    dmg = ev.get("amount", 0) + (last[1] if last and t - last[0] < 6 else 0)
                    self.attackers[by] = (t, dmg)
                    if ev.get("bearing") is not None:
                        self.threat_bearing = ev["bearing"]
                        self.threat_t = t
            elif et == "take_failed":
                self.bad_pickups[ev.get("id")] = t + (999 if ev.get("reason") in ("gone", "have") else 6)
        for k in [k for k, v in self.attackers.items() if t - v[0] > 12]:
            del self.attackers[k]

        # ---------- upgrade offer
        offer = obs.get("offer")
        if offer and offer.get("choices"):
            ids = [c["id"] for c in offer["choices"]]
            best = min(range(len(ids)), key=lambda i: UPGRADE_PRIORITY.index(ids[i]) if ids[i] in UPGRADE_PRIORITY else 99)
            act["pick"] = best

        # ---------- weapons
        weapons = me.get("weapons") or [None, None]
        slots = {}
        for i, w in enumerate(weapons):
            if w:
                slots[w["kind"]] = (i, w)
        gun = slots.get("gun")
        laser = slots.get("laser")
        light = slots.get("lightning")
        mortar = slots.get("mortar")

        # ---------- zone
        zone = obs["zone"]
        zcx, zcy, zr = self.zone_now(zone, t)
        spot, at_spot = self.safe_spot(zone, x, y)
        in_zone = me.get("in_zone", True)
        dist_spot = math.hypot(spot[0] - x, spot[1] - y)
        time_to_shrink = zone["shrink_start"] - t
        travel = dist_spot / max(1.0, stats.get("walk_speed", 11.7))
        zone_urgent = (not in_zone) or (not at_spot and (time_to_shrink < travel + 12 or zone["dps"] >= 60)) \
            or (not self.in_circle(x, y, zcx, zcy, zr, 15.0))

        # ---------- perception
        enemies, npcs = [], []
        for m in obs.get("mechs", []):
            p = m["pos"]
            d = math.hypot(p[0] - x, p[1] - y)
            if m["kind"] == "mech":
                if m["id"] == self.me:
                    continue
                enemies.append((d, m))
            else:
                npcs.append((d, m))
        enemies.sort(key=lambda e: e[0])
        npcs.sort(key=lambda e: e[0])

        def center_of(m):
            cubes = m.get("cubes", 0) or 0
            s = 1.0 + 0.05 * cubes
            h = 4.5 * s if m["kind"] == "mech" else 1.75
            p = m["pos"]
            return (p[0], p[1], p[2] + h)

        # who is dangerous
        hostile = []
        for d, m in enemies:
            p = m["pos"]
            bearing_to_me = math.atan2(y - p[1], x - p[0])
            aiming = abs(wrap(m["aim"][0] - bearing_to_me)) < 0.18
            attacked = m["id"] in self.attackers
            if m.get("charging"):
                self.charging_since.setdefault(m["id"], t)
            else:
                self.charging_since.pop(m["id"], None)
            vis = nav.los((x, y, eye), center_of(m))
            mhpf = (m.get("hp", 1400) or 1) / max(1.0, m.get("max_hp", 1400) or 1400)
            hostile.append({"m": m, "d": d, "aiming": aiming, "attacked": attacked, "vis": vis, "hpf": mhpf})

        # ---------- target choice
        target, tkind = None, None
        max_range = 230.0
        if gun:
            max_range = gun[1]["stats"].get("range", 230)
        if laser:
            max_range = max(max_range, laser[1]["stats"].get("range", 280))
        best_s = 1e9
        for h in hostile:
            d = h["d"]
            if not h["vis"] or d > max_range:
                continue
            engage = h["attacked"] or d < 95 or (h["aiming"] and d < 170) or (h["hpf"] < 0.35 and d < 170) \
                or (self.last_target == h["m"]["id"] and t - self.last_target_t < 3)
            if not engage:
                continue
            s = d * (0.5 + h["hpf"]) - (150 if h["attacked"] else 0) - (60 if h["aiming"] else 0)
            if self.last_target == h["m"]["id"]:
                s -= 40
            if s < best_s:
                best_s, target, tkind = s, h, "mech"
        if target:
            self.last_target = target["m"]["id"]
            self.last_target_t = t

        threats = [h for h in hostile if h["d"] < 150 and (h["attacked"] or h["aiming"] or h["d"] < 90)]

        # farm npc/crates when calm
        calm = not threats and not zone_urgent and t - self.threat_t > 4
        farm = None
        if target is None and calm and hpf > 0.5:
            for d, m in npcs:
                if d < 75 and nav.los((x, y, eye), center_of(m)):
                    farm = ("npc", m)
                    break
            if farm is None and t < 260 and hpf > 0.6:
                best = None
                for c in obs.get("crates", []):
                    p = c["pos"]
                    d = math.hypot(p[0] - x, p[1] - y)
                    if d < 55 and (best is None or d < best[0]) and \
                            nav.los((x, y, eye), (p[0], p[1], p[2] + 1.2)):
                        best = (d, c)
                if best:
                    farm = ("crate", best[1])
        # npcs that are shooting at us count as targets too
        if target is None and farm is None:
            for d, m in npcs:
                if d < 50 and m["id"] in self.attackers and nav.los((x, y, eye), center_of(m)):
                    farm = ("npc", m)
                    break

        # ---------- movement goal
        mvx, mvy = 0.0, 0.0
        boost = False
        state = ""
        goal = None

        if target is not None:
            m = target["m"]
            d = target["d"]
            p = m["pos"]
            ux, uy = (p[0] - x) / max(d, 0.1), (p[1] - y) / max(d, 0.1)
            nthreat = len(threats)
            my_power = hpf * (1.0 + 0.04 * min(me.get("cubes", 0), 10))
            their_power = target["hpf"] * (1.0 + 0.04 * min(m.get("cubes", 0) or 0, 10))
            retreat = (hpf < 0.35 and their_power > my_power * 0.7) or nthreat >= 3 or \
                (nthreat >= 2 and hpf < 0.6)
            if light and not retreat and my_power > their_power * 1.1:
                pref = 26.0
            elif laser or gun:
                pref = 75.0
            else:
                pref = 60.0
            if retreat:
                radial = -1.0
                state = "retreat"
            else:
                radial = max(-1.0, min(1.0, (d - pref) / 25.0))
                state = "fight"
            if t > self.strafe_t:
                self.strafe = -self.strafe if self.rng.random() < 0.7 else self.strafe
                self.strafe_t = t + self.rng.uniform(0.6, 1.5)
            sx, sy = -uy * self.strafe, ux * self.strafe
            strafe_w = 0.55 if retreat else 0.9
            mvx = ux * radial + sx * strafe_w
            mvy = uy * radial + sy * strafe_w
            if zone_urgent:
                zx, zy = self.nav_move(x, y, spot[0], spot[1], budget_end)
                mvx, mvy = zx * 1.0 + sx * 0.4, zy * 1.0 + sy * 0.4
            else:
                # don't wander out of the zone while fighting
                nxp, nyp = x + mvx * 8, y + mvy * 8
                if not self.in_circle(nxp, nyp, zcx, zcy, zr, 12.0):
                    zx, zy = zcx - x, zcy - y
                    zd = math.hypot(zx, zy) or 1.0
                    mvx, mvy = mvx * 0.3 + zx / zd, mvy * 0.3 + zy / zd
            mvx, mvy = self.deflect(x, y, mvx, mvy)
            boost = energy > (45 if light else 25)
        else:
            if zone_urgent:
                goal = spot
                state = "zone"
                boost = (not in_zone) or (energy > 70 and dist_spot > 60)
            else:
                goal = self.pick_goal(obs, x, y, z, hpf, zone, zcx, zcy, zr, slots, weapons, farm)
                if goal is None:
                    goal = spot if not at_spot else None
                    state = "spot"
                else:
                    state = goal[2]
                    goal = goal[:2]
                if goal is None:
                    # we're in our safe area: hold next to a wall
                    if self.cover is None or self.cover_for is None or \
                            math.hypot(self.cover_for[0] - spot[0], self.cover_for[1] - spot[1]) > 10 or \
                            not self.in_circle(self.cover[0], self.cover[1], zone["next_center"][0],
                                               zone["next_center"][1], zone["next_radius"], 4.0):
                        self.cover_for = spot
                        self.cover = nav.cover_near(spot[0], spot[1], 10)
                        if self.cover is not None and not self.in_circle(
                                self.cover[0], self.cover[1], zone["next_center"][0], zone["next_center"][1],
                                zone["next_radius"], 4.0):
                            self.cover = None
                    goal = self.cover or spot
                    state = "hold"
            if goal is not None:
                gd = math.hypot(goal[0] - x, goal[1] - y)
                if gd > 1.5:
                    mvx, mvy = self.nav_move(x, y, goal[0], goal[1], budget_end)
                    if state == "hold" and gd < 6:
                        mvx, mvy = mvx * 0.4, mvy * 0.4  # quiet approach
            # unseen attacker: sidestep while turning to face it
            if t - self.threat_t < 2.5 and self.threat_bearing is not None:
                bx, by_ = math.cos(self.threat_bearing), math.sin(self.threat_bearing)
                if t > self.strafe_t:
                    self.strafe = -self.strafe
                    self.strafe_t = t + self.rng.uniform(0.6, 1.3)
                mvx += -by_ * self.strafe * 0.8
                mvy += bx * self.strafe * 0.8
                mvx, mvy = self.deflect(x, y, mvx, mvy)
                boost = boost or energy > 40

        # laser dodge: someone charging at us
        jump = False
        for h in hostile:
            cs = self.charging_since.get(h["m"]["id"])
            if cs is not None and h["aiming"] and h["vis"] and t - cs > 0.35:
                p = h["m"]["pos"]
                bx, by_ = (x - p[0]) / max(h["d"], 0.1), (y - p[1]) / max(h["d"], 0.1)
                mvx += -by_ * self.strafe * 1.2
                mvy += bx * self.strafe * 1.2
                mvx, mvy = self.deflect(x, y, mvx, mvy)
                boost = energy > 15
                if me.get("grounded") and t - cs > 0.45:
                    jump = True
                break

        # walls / roofs in the way of a travel move: jump-jet over them
        climbing = False
        if state not in ("fight", "retreat") and not jump:
            cl = self.climb_ctl(x, y, z, mvx, mvy, me.get("grounded", True), energy, not in_zone)
            if cl is not None:
                climbing = True
                if cl == "jump":
                    jump = True
                elif cl == "jet":
                    boost = True
                elif cl == "wait":
                    mvx, mvy = 0.0, 0.0
                    state += "/charge"
                state += "/climb"

        # stuck handling
        moving = math.hypot(mvx, mvy) > 0.3
        self.hist.append((t, x, y))
        while self.hist and t - self.hist[0][0] > 1.2:
            self.hist.pop(0)
        if climbing or not me.get("grounded", True):
            self.hist = [(t, x, y)]
        if moving and len(self.hist) >= 8 and t > self.stuck_until + 1.0:
            ox, oy = self.hist[0][1], self.hist[0][2]
            if math.hypot(x - ox, y - oy) < 1.2:
                self.stuck_until = t + 0.9
                self.jet_until = t + 0.9
                ang = math.atan2(mvy, mvx) + self.rng.choice((-1, 1)) * self.rng.uniform(0.8, 1.8)
                self.stuck_dir = (math.cos(ang), math.sin(ang), mvx, mvy)
                self.path = None
                jump = True
        if t < self.stuck_until and self.stuck_dir is not None:
            if t < self.stuck_until - 0.5:
                mvx, mvy = self.stuck_dir[2], self.stuck_dir[3]  # jet over it first
            else:
                mvx, mvy = self.stuck_dir[0], self.stuck_dir[1]
        if t < self.jet_until and not me.get("grounded") and energy > 10:
            boost = True

        mm = math.hypot(mvx, mvy)
        if mm > 1.0:
            mvx, mvy = mvx / mm, mvy / mm
        act["move"] = [round(mvx, 3), round(mvy, 3)]
        act["boost"] = bool(boost and mm > 0.2) or (t < self.jet_until and not me.get("grounded"))
        if jump:
            act["jump"] = True

        # ---------- aim & fire
        fire0 = fire1 = False
        aim = None
        shoot_at = None
        if target is not None:
            shoot_at = ("mech", target["m"])
        elif farm is not None:
            shoot_at = farm
        if shoot_at is not None:
            kind, m = shoot_at
            if kind == "crate":
                p = m["pos"]
                c = (p[0], p[1], p[2] + 1.2)
                v = (0.0, 0.0, 0.0)
                airborne = False
            else:
                c = center_of(m)
                v = m.get("vel") or (0.0, 0.0, 0.0)
                airborne = abs(v[2]) > 0.5
            d3 = math.sqrt((c[0] - x) ** 2 + (c[1] - y) ** 2 + (c[2] - muzzle) ** 2)
            # which weapon drives the aim
            laser_ready = laser and laser[1].get("cooldown", 1) <= 0.0 and d3 < laser[1]["stats"].get("range", 280)
            laser_charge = laser[1].get("charge", 0) if laser else 0
            full = laser[1]["stats"].get("charge", 0.75) if laser else 0.75
            hitscan_q = (c[0] + v[0] * 0.1, c[1] + v[1] * 0.1, c[2] + v[2] * 0.1)
            gspeed = gun[1]["stats"].get("speed", 252) if gun else 252
            lead_q = self.lead(x, y, muzzle, c, v, gspeed, airborne)
            use_hitscan = laser and laser_charge >= full * 0.8
            if light and d3 < light[1]["stats"].get("range", 45) * 0.95:
                use_hitscan = True
            q = hitscan_q if use_hitscan else lead_q
            yaw, pitch, dist = self.aim_to(x, y, muzzle, q)
            aim = [yaw, pitch]
            clear = nav.los((x, y, muzzle), c, skip_end=2.5)
            # aim error -> miss distance
            yerr = abs(wrap(ayaw - yaw))
            perr = abs(apitch - pitch)
            miss = dist * math.sqrt(yerr * yerr + perr * perr)
            rad = 2.2 if kind == "mech" else 1.3
            # gun
            if gun and clear:
                gw = gun[1]
                if gw.get("reload", 0) <= 0 and (gw.get("ammo", 1) or 0) > 0 and \
                        d3 < gw["stats"].get("range", 230) and gw.get("cooldown", 0) <= 0.1:
                    gyaw, gpitch, gdist = self.aim_to(x, y, muzzle, lead_q)
                    gmiss = gdist * math.hypot(wrap(ayaw - gyaw), apitch - gpitch)
                    if gmiss < rad + 0.3 + gdist * 0.004:
                        if gw is weapons[0]:
                            fire0 = True
                        else:
                            fire1 = True
            # lightning
            if light and clear:
                lw = light[1]
                lr = lw["stats"].get("range", 45)
                cone = math.radians(lw["stats"].get("cone_deg", 30)) * 0.4
                hd = math.hypot(c[0] - x, c[1] - y)
                if hd < lr * 0.97 and abs(wrap(ayaw - math.atan2(c[1] - y, c[0] - x))) < cone and \
                        energy >= lw["stats"].get("energy", 3) + 2 and lw.get("cooldown", 0) <= 0.1:
                    if light[0] == 0:
                        fire0 = True
                    else:
                        fire1 = True
            # laser: hold to charge, release when full and on target
            if laser:
                lw = laser[1]
                hold = False
                if laser_charge > 0:
                    hold = True
                    if laser_charge >= full * 0.97 and clear:
                        hyaw, hpitch, hdist = self.aim_to(x, y, muzzle, hitscan_q)
                        hmiss = hdist * math.hypot(wrap(ayaw - hyaw), apitch - hpitch)
                        if hmiss < rad:
                            hold = False  # release -> fires
                elif laser_ready and clear and (kind == "mech" or not light):
                    hold = True
                if hold:
                    if laser[0] == 0:
                        fire0 = True
                    else:
                        fire1 = True
        else:
            # look around: toward the threat, recent sounds, or a slow sweep
            if t - self.threat_t < 3.0 and self.threat_bearing is not None:
                aim = [self.threat_bearing, 0.0]
            else:
                for h in hostile:
                    p = h["m"]["pos"]
                    aim = [math.atan2(p[1] - y, p[0] - x), 0.0]
                    break
                if aim is None:
                    for s in obs.get("sounds", []):
                        if s.get("kind") in ("gun", "laser", "lightning", "mortar", "laser_charge", "step", "boost", "jet") \
                                and s.get("dist") in ("near", "mid"):
                            self.sound_look = s["bearing"]
                            self.sound_look_t = t
                    if self.sound_look is not None and t - self.sound_look_t < 1.5:
                        aim = [self.sound_look, 0.0]
                if aim is None:
                    base_yaw = math.atan2(mvy, mvx) if mm > 0.3 else ayaw
                    if mm > 0.3:
                        aim = [base_yaw + 1.0 * math.sin(t * 1.3), 0.0]
                    else:
                        aim = [wrap(ayaw + 0.9), 0.0]
            if gun and gun[1].get("reload", 0) <= 0 and \
                    (gun[1].get("ammo", 12) or 0) < gun[1]["stats"].get("mag", 12) * 0.5 and \
                    t - self.last_target_t > 1.5:
                act["reload"] = True
        act["aim"] = [round(wrap(aim[0]), 4), round(max(-0.69, min(1.29, aim[1])), 4)]
        if fire0 or fire1:
            act["fire"] = [fire0, fire1]

        # ---------- loot
        tk = self.want_take(obs, x, y, z, slots, weapons)
        if tk is not None:
            act["take"] = tk[0]
            if tk[1] is not None:
                act["drop"] = tk[1]

        self.state = state
        mf.draw.label(f"{state} hp{hp:.0f} e{energy:.0f} {'T%d' % target['m']['id'] if target else ''}")
        el = (time.perf_counter() - t0) * 1000
        if el > 35:
            self.slow_ticks += 1
            if self.slow_ticks < 20:
                log(f"slow tick {obs['tick']}: {el:.1f} ms")
        return act

    # ------------------------------------------------------------------ goals & loot
    def reachable_item(self, p):
        return p[2] - self.nav.ground(p[0], p[1]) < 2.5

    def pick_goal(self, obs, x, y, z, hpf, zone, zcx, zcy, zr, slots, weapons, farm):
        t = self.t
        nc, nr = zone["next_center"], zone["next_radius"]
        # supply drop
        for dr in obs.get("drops", []):
            p = dr["pos"]
            d = math.hypot(p[0] - x, p[1] - y)
            holder = dr.get("holder")
            if holder is not None and holder != self.me:
                continue
            if d > 170 or not self.in_circle(p[0], p[1], zcx, zcy, zr, 10):
                continue
            if dr.get("lands_in", 0) > d / 11.0 + 6:
                continue
            danger = False
            for m in obs.get("mechs", []):
                if m["kind"] == "mech" and math.hypot(m["pos"][0] - p[0], m["pos"][1] - p[1]) < 60:
                    danger = True
            if not danger:
                return (p[0], p[1], "drop")
        # weapon
        have_empty = any(w is None for w in weapons)
        if have_empty:
            best = None
            for pk in obs.get("pickups", []):
                if pk["kind"] not in WANT_WEAPON or pk["kind"] in slots:
                    continue
                if self.bad_pickups.get(pk["id"], -1) > t:
                    continue
                p = pk["pos"]
                if not self.reachable_item(p) or not self.in_circle(p[0], p[1], zcx, zcy, zr, 15):
                    continue
                d = math.hypot(p[0] - x, p[1] - y)
                s = d - 15 * WANT_WEAPON[pk["kind"]]
                if d < 110 and (best is None or s < best[0]):
                    best = (s, p)
            if best:
                return (best[1][0], best[1][1], "loot")
        # cubes
        best = None
        for c in obs.get("cubes", []):
            p = c["pos"]
            if not self.reachable_item(p) or not self.in_circle(p[0], p[1], zcx, zcy, zr, 10):
                continue
            d = math.hypot(p[0] - x, p[1] - y)
            if d < 80 and (best is None or d < best[0]):
                best = (d, p)
        if best:
            return (best[1][0], best[1][1], "cube")
        # farming target: get within comfortable range
        if farm is not None:
            kind, m = farm
            p = m["pos"]
            d = math.hypot(p[0] - x, p[1] - y)
            want = 22.0 if slots.get("lightning") else 35.0
            if d > want:
                return (p[0], p[1], "farm")
            return (x, y, "farm")
        return None

    def want_take(self, obs, x, y, z, slots, weapons):
        t = self.t
        empty = [i for i, w in enumerate(weapons) if w is None]
        for pk in obs.get("pickups", []):
            p = pk["pos"]
            if math.hypot(p[0] - x, p[1] - y) > self.reach - 0.3 or abs(p[2] - z) > 3.8:
                continue
            if self.bad_pickups.get(pk["id"], -1) > t:
                continue
            k = pk["kind"]
            if k in slots:
                continue
            if k in WANT_WEAPON:
                if empty:
                    return (pk["id"], None)
                # swap out a mortar for something better
                m = slots.get("mortar")
                if m is not None:
                    return (pk["id"], m[0])
        return None


if __name__ == "__main__":
    mf.run(Bot)
