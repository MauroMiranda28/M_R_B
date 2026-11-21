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
# see first, aim faster: +25 m vision, +15 m proximity, half the sound bearing error, +30% turn rate
VISION_FIRST = True
if VISION_FIRST:
    UPGRADE_PRIORITY = ["sensors", "armor", "gyros", "plating"] + \
        [u for u in UPGRADE_PRIORITY if u not in ("sensors", "armor", "gyros", "plating")]
# survival-first: never start fights, hide from anyone we see, shoot only when cornered
# v6 = the v1 style (best on the track so far) + projectile awareness.
# Track scores: v1 3.54 (aggressive, farms) > v3 3.31 > v2 2.85 > v5 2.21 (pacifist, hides, edge, jink).
PACIFIST = False
AGGRO_RANGE = 95.0       # engage non-hostile mechs closer than this
UNSEEN_HIDE_HP = 0.0     # hide from an attacker we can't see below this HP fraction
SPAWN_COVER_T = 0.0      # seconds after spawn spent getting into cover before looting
JINK = False             # erratic sidesteps all the time, not only when hit
ZONE_EDGE = False        # live in a band just inside the next circle's edge, not deep inside
FIGHT_HIDE = False       # break line of sight mid-fight when losing
FARM_NPC_R, FARM_CRATE_R, FARM_CRATE_T, FARM_HP = 75.0, 55.0, 260.0, 0.6
DODGE_SHELLS = True      # run out of the splash of incoming mortar shells
BULLET_ALERT = True      # turn toward bullets flying at us before they land
FARM_ROAM = True         # actively hunt crates and drones for cubes early on
FARM_UNTIL = 300.0       # ... until this match time
FARM_RANGE = 260.0       # how far we walk to a remembered crate / drone
DROP_RANGE = 260.0       # how far we go for a supply drop (3 cubes + full HP/energy)
CUBE_RANGE = 150.0       # how far we walk to a seen / remembered cube
VULTURE = True           # walk toward fights we hear, finish the wounded, loot death cubes
VULTURE_HP = 0.6         # only when at least this healthy
VULTURE_STANDOFF = 70.0  # stop this far from the estimated fight
FIGHT_SOUNDS = ("gun", "laser", "lightning", "mortar", "explosion")
SOUND_DIST = {"near": 40.0, "mid": 110.0, "far": 230.0}
# v11 small-tweaks package
GUN_MAX_RANGE = 150.0    # don't give our position away with low-odds long gun shots (unless they attack us)
COOKOFF_FOCUS = True     # with a laser, prefer targets carrying a mortar (+60% cook-off)
WEAPON_UPGRADES = True   # weapon upgrades for what we actually hold, right after the defensive ones
COMBAT_ENERGY_KEEP = 40.0  # keep this much energy for an escape jet instead of boosting it away
LONG_STUCK = True        # no real progress for 8 s while travelling: drop the route, take a detour
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
        o += 2 * n
        self.canopy = raw[o:o + n] if len(raw) >= o + n else bytes(n)
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
        top, base, surf = self.top, self.base, self.surf
        kend = n - int(skip_end / step)
        if kend < 1:
            return True
        inv, nx, ny = self.inv, self.nx, self.ny
        # walk in grid units; z in decimeters
        gx = (a[0] - self.minx) * inv
        gy = (a[1] - self.miny) * inv
        gz = a[2] * 10.0
        sx, sy, sz = dx * inv / n, dy * inv / n, dz * 10.0 / n
        nxm, nym = nx - 1, ny - 1
        for k in range(1, kend + 1):
            i = int(gx + sx * k)
            j = int(gy + sy * k)
            if i < 0 or j < 0 or i > nxm or j > nym:
                continue
            c = j * nx + i
            zz = gz + sz * k
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
                can = self.canopy[c]
                if walls == 0 and can < 2:
                    continue
                s = math.hypot(di, dj) - 0.8 * min(walls, 3) - 0.35 * min(can, 8)
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
    name = "survivor-v11"

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
        self.hide_xy = None
        self.known_crates = {}
        self.known_npcs = {}
        self.known_cubes = {}
        self.fight_snd = []
        self.death_sites = []
        self.vulture_until = -99.0
        self.prog = []
        self.detour = None
        self.detour_until = -99.0
        self.explore_pt = None
        self.explore_t = -99.0
        self.jink = 0.0
        self.jink_t = -1.0
        self.jink_dir = (1.0, 0.0)
        self.hide_until = -99.0
        self.hide_t = -99.0
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
        if ZONE_EDGE:
            margin = R * 0.45 if R < 40 else min(35.0, max(16.0, 0.15 * R))
            outer = max(0.0, R - margin)
            inner = max(0.0, outer - 22.0)
            d = math.hypot(x - nc[0], y - nc[1])
            if inner <= d <= outer:
                return (x, y), True
            if d < 1e-6:
                a = self.rng.uniform(-math.pi, math.pi)
                ux, uy = math.cos(a), math.sin(a)
            else:
                ux, uy = (x - nc[0]) / d, (y - nc[1]) / d
            r = outer if d > outer else 0.5 * (inner + outer)
            return (nc[0] + ux * r, nc[1] + uy * r), False
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

    def hidden_from(self, px, py, eyes):
        g = self.nav.ground(px, py)
        for e in eyes:
            if self.nav.los(e, (px, py, g + 8.6), skip_end=1.0) or self.nav.los(e, (px, py, g + 4.5), skip_end=1.0):
                return False
        return True

    def hide_spot(self, x, y, eyes, zc, t):
        """Nearest reachable free spot that no threat eye can see; cached briefly."""
        if self.hide_xy is not None and t - self.hide_t < 0.7:
            return self.hide_xy
        deadline = time.perf_counter() + 0.006
        if self.hide_xy is not None and math.hypot(self.hide_xy[0] - x, self.hide_xy[1] - y) < 50 and \
                self.hidden_from(self.hide_xy[0], self.hide_xy[1], eyes):
            self.hide_t = t
            return self.hide_xy
        nav = self.nav
        zcx, zcy, zr = zc
        ex = sum(e[0] for e in eyes) / len(eyes)
        ey = sum(e[1] for e in eyes) / len(eyes)
        dnow = math.hypot(ex - x, ey - y)
        cands = []
        for r in (4.0, 8.0, 13.0, 19.0, 26.0, 34.0, 44.0, 56.0, 70.0):
            for k in range(16 if r < 40 else 24):
                a = k * TAU / 16 + r * 0.37
                px, py = x + r * math.cos(a), y + r * math.sin(a)
                if nav.blk[nav.idx(px, py)] != 0:
                    continue
                if not self.in_circle(px, py, zcx, zcy, zr, 8.0):
                    continue
                closer = max(0.0, dnow - math.hypot(ex - px, ey - py))
                cands.append((r + 1.2 * closer, px, py, r))
        cands.sort()
        found = None
        for sc, px, py, r in cands[:70]:
            if time.perf_counter() > deadline:
                break
            if self.hidden_from(px, py, eyes):
                found = (px, py)
                break
        self.hide_t = t
        self.hide_xy = found
        return found

    def projectile_react(self, obs, x, y, z, vx, vy, t):
        """Returns a move vector away from a mortar landing near us, or None.
        Also turns bullets heading at us into a threat bearing."""
        mort = self.w_cfg.get("mortar", {})
        g = mort.get("gravity", 22.0)
        splash = mort.get("splash_radius", 7.0)
        best = None
        for pr in obs.get("projectiles", []):
            k = pr.get("kind")
            p, v = pr["pos"], pr["vel"]
            if k == "mortar" and DODGE_SHELLS:
                # time until the shell comes down to our feet height
                a, b, c = -0.5 * g, v[2], p[2] - z
                disc = b * b - 4 * a * c
                if disc < 0:
                    continue
                tt = (-b - math.sqrt(disc)) / (2 * a)
                if tt <= 0 or tt > 6:
                    continue
                ix, iy = p[0] + v[0] * tt, p[1] + v[1] * tt
                px, py = x + vx * min(tt, 0.6), y + vy * min(tt, 0.6)
                d = math.hypot(px - ix, py - iy)
                if d < splash + 5.0 and (best is None or tt < best[0]):
                    if d < 0.5:
                        hx, hy = -v[1], v[0]
                    else:
                        hx, hy = px - ix, py - iy
                    hl = math.hypot(hx, hy) or 1.0
                    best = (tt, hx / hl, hy / hl)
            elif k in ("gun", "npc") and BULLET_ALERT:
                rx, ry, rz = x - p[0], y - p[1], z + 4.5 - p[2]
                vv = v[0] * v[0] + v[1] * v[1] + v[2] * v[2]
                if vv < 1:
                    continue
                s_ = (rx * v[0] + ry * v[1] + rz * v[2]) / vv
                if s_ <= 0 or s_ > 1.5:
                    continue
                cx, cy, cz = p[0] + v[0] * s_ - x, p[1] + v[1] * s_ - y, p[2] + v[2] * s_ - (z + 4.5)
                if cx * cx + cy * cy < 16 and abs(cz) < 6 and k == "gun":
                    self.threat_bearing = math.atan2(-v[1], -v[0])
                    self.threat_t = t
        if best is None:
            return None
        mvx, mvy = best[1], best[2]
        mvx, mvy = self.deflect(x, y, mvx, mvy, 4.0)
        return mvx, mvy

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
        budget_end = t0 + 0.011
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
        evlog = []
        for ev in obs.get("events", []):
            et = ev.get("type")
            try:
                if et == "damaged":
                    b = ev.get("bearing")
                    evlog.append("DMG %.0f %s by%s%s%s" % (ev.get("amount", 0), ev.get("weapon"), ev.get("by"),
                                                          " b%.2f" % b if b is not None else "",
                                                          " REAR" if ev.get("rear") else ""))
                elif et == "hit":
                    evlog.append("HIT %s %.0f %s%s" % (ev.get("target"), ev.get("amount", 0), ev.get("weapon"),
                                                      " " + ev["effect"] if ev.get("effect") else ""))
                elif et in ("kill", "effect", "drop", "pickup", "upgrade", "took", "dropped", "take_failed"):
                    evlog.append(et.upper() + " " + " ".join("%s=%s" % (k, v) for k, v in ev.items() if k != "type"))
            except Exception:
                pass
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
            prio = UPGRADE_PRIORITY
            if WEAPON_UPGRADES:
                held = {w["kind"] for w in (me.get("weapons") or []) if w}
                wfirst = []
                if "laser" in held:
                    wfirst += ["laser_damage", "laser_charge"]
                if "lightning" in held:
                    wfirst += ["lightning_efficiency", "lightning_range"]
                if "gun" in held and "laser" not in held:
                    wfirst += ["gun_damage", "gun_rate"]
                head = [u for u in prio[:4]]
                prio = head + wfirst + [u for u in prio[4:] if u not in wfirst]
            best = min(range(len(ids)), key=lambda i: prio.index(ids[i]) if ids[i] in prio else 99)
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
            or (not self.in_circle(x, y, zcx, zcy, zr, 10.0 if ZONE_EDGE else 15.0))

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
            engage = h["attacked"] or d < AGGRO_RANGE or (h["aiming"] and d < 170) or (h["hpf"] < 0.35 and d < 170) \
                or (self.last_target == h["m"]["id"] and t - self.last_target_t < 3)
            if VULTURE and t < self.vulture_until and h["hpf"] < 0.65 and d < 170 and hpf > 0.45:
                engage = True
            if PACIFIST:
                engage = d < 40 or (h["attacked"] and (d < 75 or h["hpf"] < 0.3)) or \
                    (self.last_target == h["m"]["id"] and t - self.last_target_t < 2 and d < 75)
            if not engage:
                continue
            s = d * (0.5 + h["hpf"]) - (150 if h["attacked"] else 0) - (60 if h["aiming"] else 0)
            if COOKOFF_FOCUS and laser and "mortar" in (h["m"].get("weapons") or []):
                s -= 50
            if self.last_target == h["m"]["id"]:
                s -= 40
            if s < best_s:
                best_s, target, tkind = s, h, "mech"
        if target:
            self.last_target = target["m"]["id"]
            self.last_target_t = t

        threats = [h for h in hostile if h["d"] < 150 and (h["attacked"] or h["aiming"] or h["d"] < 90)]

        # listen for fights and deaths (vulture)
        if VULTURE:
            self.listen(obs, x, y, t)

        # remember crates and drones we have seen (they don't move far)
        if FARM_ROAM:
            self.remember_farm(obs, x, y, (x, y, eye), t)

        # farm npc/crates when calm
        calm = not threats and not zone_urgent and t - self.threat_t > 4
        farm = None
        if target is None and calm and hpf > 0.5 and not PACIFIST:
            for d, m in npcs:
                if d < FARM_NPC_R and nav.los((x, y, eye), center_of(m)):
                    farm = ("npc", m)
                    break
            if farm is None and t < FARM_CRATE_T and hpf > FARM_HP:
                best = None
                for c in obs.get("crates", []):
                    p = c["pos"]
                    d = math.hypot(p[0] - x, p[1] - y)
                    if d < FARM_CRATE_R and (best is None or d < best[0]) and \
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
            # trade shots in the open only when clearly winning; otherwise break line of sight and heal
            press = (my_power > their_power * 1.35 and nthreat <= 1 and hpf > 0.5) or \
                (target["hpf"] < 0.25 and hpf > 0.35 and nthreat <= 1) or \
                (light and d < 35 and my_power > their_power * 1.1 and nthreat <= 1)
            hide_xy = None
            want_hide = hpf < 0.5 or nthreat >= 2 or their_power > my_power * 1.25
            if PACIFIST:
                press = (target["hpf"] < 0.25 and d < 80 and nthreat <= 1 and hpf > 0.3) or \
                    (light and d < 38 and my_power > their_power * 1.2 and nthreat <= 1)
                want_hide = True
            if FIGHT_HIDE and not press and want_hide and not zone_urgent:
                eyes = [(h["m"]["pos"][0], h["m"]["pos"][1], h["m"]["pos"][2] + 8.0)
                        for h in (threats or [target])][:3]
                if target not in threats:
                    eyes.append((p[0], p[1], p[2] + 8.0))
                hide_xy = self.hide_spot(x, y, eyes, (zcx, zcy, zr), t)
            if retreat and hide_xy is None:
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
            if hide_xy is not None:
                state = "hide"
                hx, hy = self.nav_move(x, y, hide_xy[0], hide_xy[1], budget_end)
                if math.hypot(hide_xy[0] - x, hide_xy[1] - y) < 2.0:
                    hx, hy = 0.0, 0.0
                mvx, mvy = hx + sx * 0.25, hy + sy * 0.25
                self.hide_until = t + 6.0
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
            boost = energy > max(COMBAT_ENERGY_KEEP, 45 if light else 25)
        else:
            # unseen attacker: hide from where the shots came from
            if not zone_urgent and hpf < UNSEEN_HIDE_HP and t - self.threat_t < 2.0 and self.threat_bearing is not None \
                    and not any(h["vis"] for h in threats):
                bx, by_ = math.cos(self.threat_bearing), math.sin(self.threat_bearing)
                pseudo = [(x + bx * 70, y + by_ * 70, z + 8.0)]
                hs = self.hide_spot(x, y, pseudo, (zcx, zcy, zr), t)
                if hs is not None:
                    self.hide_until = t + 6.0
            if PACIFIST and not zone_urgent:
                seen_eyes = [(h["m"]["pos"][0], h["m"]["pos"][1], h["m"]["pos"][2] + 8.0)
                             for h in hostile if h["vis"] and h["d"] < 170][:3]
                if seen_eyes:
                    hs = self.hide_spot(x, y, seen_eyes, (zcx, zcy, zr), t)
                    if hs is not None:
                        self.hide_until = max(self.hide_until, t + 4.0)
            hiding = (not zone_urgent and self.hide_xy is not None and t < self.hide_until)
            if hiding and hpf < 0.9 and t - self.threat_t < 25:
                self.hide_until = max(self.hide_until, t + 0.5)  # stay put while regenerating
            if zone_urgent:
                goal = spot
                state = "zone"
                boost = (not in_zone) or (energy > 70 and dist_spot > 60)
            elif hiding:
                goal = self.hide_xy
                state = "hide"
                boost = energy > 30 and math.hypot(goal[0] - x, goal[1] - y) > 8
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
            if state != "hide" and t - self.threat_t < 2.5 and self.threat_bearing is not None:
                bx, by_ = math.cos(self.threat_bearing), math.sin(self.threat_bearing)
                if t > self.strafe_t:
                    self.strafe = -self.strafe
                    self.strafe_t = t + self.rng.uniform(0.6, 1.3)
                mvx += -by_ * self.strafe * 0.8
                mvy += bx * self.strafe * 0.8
                mvx, mvy = self.deflect(x, y, mvx, mvy)
                boost = boost or energy > 40

        # incoming projectiles: dodge mortar splash, notice bullets aimed at us
        if DODGE_SHELLS or BULLET_ALERT:
            dz_ = self.projectile_react(obs, x, y, z, vx, vy, t)
            if dz_ is not None:
                mvx, mvy = dz_
                boost = energy > 5
                state = "dodge"

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

        # erratic sidesteps even when nobody seems to be shooting at us
        if JINK and state.split("/")[0] in ("spot", "zone", "loot", "cube", "hold", "farm", "spawncover", "hide") \
                and not jump:
            if t > self.jink_t:
                self.jink = self.rng.choice((-1.0, 1.0)) * self.rng.uniform(0.35, 0.8)
                ja = self.rng.uniform(-math.pi, math.pi)
                self.jink_dir = (math.cos(ja), math.sin(ja))
                self.jink_t = t + self.rng.uniform(0.35, 1.1)
            mlen = math.hypot(mvx, mvy)
            gd = math.hypot(goal[0] - x, goal[1] - y) if goal is not None else 0.0
            calm_zone = in_zone and zone.get("dps", 0) < 100
            if mlen > 0.3 and gd > 8.0 and calm_zone:
                ux, uy = mvx / mlen, mvy / mlen
                jx, jy = mvx - uy * self.jink, mvy + ux * self.jink
                jl = math.hypot(jx, jy)
                # only sidestep where the ground is open; never into a wall
                if jl > 0.1 and nav.walk_clear(x, y, x + jx / jl * 6.0, y + jy / jl * 6.0, 6.5):
                    mvx, mvy = jx, jy
            elif state.split("/")[0] in ("hold", "spot") and mlen <= 0.45 and calm_zone:
                # shuffle around the spot below step-sound speed (silent)
                ax, ay = (goal if goal is not None else (x, y))
                if math.hypot(ax - x, ay - y) > 3.5:
                    dx_, dy_ = ax - x, ay - y
                    dd = math.hypot(dx_, dy_)
                    mvx, mvy = dx_ / dd * 0.4, dy_ / dd * 0.4
                else:
                    quiet = 0.9 * self.cfg.get("sound", {}).get("step_speed", 5.0) / max(1.0, stats.get("walk_speed", 11.7))
                    quiet = min(0.4, quiet if quiet > 0 else 0.38)
                    jx, jy = self.jink_dir[0] * quiet, self.jink_dir[1] * quiet
                    if nav.walk_clear(x, y, x + self.jink_dir[0] * 4.0, y + self.jink_dir[1] * 4.0, 4.5):
                        mvx, mvy = jx, jy
                    else:
                        self.jink_t = t  # pick another direction next decision

        # walls / roofs in the way of a travel move: jump-jet over them
        climbing = False
        if state not in ("fight", "retreat", "dodge") and not jump:
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

        # long-term stuck: barely moved in 8 s while trying to travel
        if LONG_STUCK:
            if not self.prog or t - self.prog[-1][0] >= 1.0:
                self.prog.append((t, x, y))
                self.prog = self.prog[-9:]
            travel = state.split("/")[0] in ("spot", "zone", "loot", "cube", "seek", "explore", "vulture",
                                             "loot-death", "farm", "drop")
            near_goal = goal is not None and math.hypot(goal[0] - x, goal[1] - y) < 25.0
            if travel and not near_goal and len(self.prog) >= 9 and t > self.detour_until + 4 and \
                    math.hypot(x - self.prog[0][1], y - self.prog[0][2]) < 5.0 and math.hypot(mvx, mvy) > 0.3:
                self.path = None
                self.plan.active = False
                self.explore_pt = None
                if goal is not None:
                    for cid in [k for k, v in self.known_crates.items() if math.hypot(v[0][0] - goal[0], v[0][1] - goal[1]) < 3]:
                        del self.known_crates[cid]
                    for cid in [k for k, v in self.known_cubes.items() if math.hypot(v[0] - goal[0], v[1] - goal[1]) < 3]:
                        del self.known_cubes[cid]
                for _ in range(12):
                    a = self.rng.uniform(-math.pi, math.pi)
                    px, py = x + 25 * math.cos(a), y + 25 * math.sin(a)
                    if nav.free(px, py) and nav.walk_clear(x, y, px, py) and \
                            self.in_circle(px, py, zcx, zcy, zr, 8.0):
                        self.detour = (px, py)
                        self.detour_until = t + 3.0
                        break
                self.prog = []
            if t < self.detour_until and self.detour is not None and state not in ("fight", "retreat", "dodge"):
                dx_, dy_ = self.detour[0] - x, self.detour[1] - y
                dd = math.hypot(dx_, dy_)
                if dd > 2:
                    mvx, mvy = dx_ / dd, dy_ / dd
                    state += "/detour"

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
                long_ok = d3 < GUN_MAX_RANGE or kind != "mech" or (target is not None and target["attacked"])
                if gw.get("reload", 0) <= 0 and (gw.get("ammo", 1) or 0) > 0 and long_ok and \
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
        try:
            self.debug_draw(obs, me, state, target, threats, hostile, evlog, spot, goal, act, slots,
                            (zcx, zcy, zr), in_zone, hpf, energy, x, y, z)
        except Exception:
            mf.draw.label(state)
        el = (time.perf_counter() - t0) * 1000
        if el > 35:
            self.slow_ticks += 1
            if self.slow_ticks < 20:
                log(f"slow tick {obs['tick']}: {el:.1f} ms")
        return act

    # ------------------------------------------------------------------ debug
    def debug_draw(self, obs, me, state, target, threats, hostile, evlog, spot, goal, act, slots,
                   zc, in_zone, hpf, energy, x, y, z):
        """Per-decision trace for the team debug file: enough to tell how and why we died."""
        d = mf.draw
        t = obs["t"]
        tgt = ""
        if target is not None:
            m = target["m"]
            tgt = " T%s@%.0f hp%.0f%%%s" % (m["id"], target["d"], target["hpf"] * 100, "" if target["vis"] else " novis")
        d.label("%s %s hp%.0f e%.0f%s" % (self.name[-2:], state, me["hp"], energy, tgt))
        w = "/".join(k for k in slots) or "-"
        gun = slots.get("gun")
        ammo = ""
        if gun:
            ammo = " a%s%s" % (gun[1].get("ammo"), " R" if gun[1].get("reload", 0) > 0 else "")
        d.text("t%.1f alive%s cubes%s %s%s mhp%.0f" % (t, obs.get("alive"), me.get("cubes", 0), w, ammo, me["max_hp"]))
        zone = obs["zone"]
        d.text("zone %s r%.0f nr%.0f dps%s dspot%.0f" % ("IN" if in_zone else "OUT", zc[2], zone["next_radius"],
                                                       zone.get("dps"), math.hypot(spot[0] - x, spot[1] - y)))
        if hostile:
            d.text("seen " + " ".join("%s:%.0f%s%s%s%.0f" % (h["m"]["id"], h["d"], "A" if h["attacked"] else "",
                                                           "a" if h["aiming"] else "", "v" if h["vis"] else "",
                                                           h["hpf"] * 100) for h in hostile[:5]))
        for e in evlog[:8]:
            d.text(e[:79], None, "#ff4040" if e.startswith("DMG") else "#40ff80")
        mv = act.get("move", [0, 0])
        flags = "".join(c for c, k in (("B", "boost"), ("J", "jump"), ("K", "take")) if act.get(k))
        fire = act.get("fire") or [False, False]
        d.text("mv%.2f,%.2f %s fire%d%d aim%.2f,%.2f" % (mv[0], mv[1], flags, fire[0], fire[1],
                                                        act["aim"][0], act["aim"][1]))
        feet = z + 1.0
        if target is not None:
            p = target["m"]["pos"]
            d.line([x, y, z + 7], [p[0], p[1], p[2] + 4.5], "#ff5040")
        if goal is not None:
            d.line([x, y, feet], [goal[0], goal[1], self.nav.ground(goal[0], goal[1]) + 1.0], "#40c0ff")
        if self.hide_xy is not None and t < self.hide_until:
            d.point([self.hide_xy[0], self.hide_xy[1], self.nav.ground(*self.hide_xy) + 1.0], "#ffd060", 7)
        if self.path:
            for px, py in self.path[self.path_i:self.path_i + 12:3]:
                d.point([px, py, self.nav.ground(px, py) + 0.5], "#4080ff", 2)
        if t - self.threat_t < 1.0 and self.threat_bearing is not None:
            b = self.threat_bearing
            d.line([x, y, z + 8], [x + 30 * math.cos(b), y + 30 * math.sin(b), z + 8], "#ff00ff")

    # ------------------------------------------------------------------ goals & loot
    def reachable_item(self, p):
        return p[2] - self.nav.ground(p[0], p[1]) < 2.5

    def pick_goal(self, obs, x, y, z, hpf, zone, zcx, zcy, zr, slots, weapons, farm):
        t = self.t
        nc, nr = zone["next_center"], zone["next_radius"]
        if t < SPAWN_COVER_T:
            if getattr(self, "spawn_cover", None) is None:
                self.spawn_cover = self.nav.cover_near(x, y, 12) or (x, y)
            return (self.spawn_cover[0], self.spawn_cover[1], "spawncover")
        # supply drop
        for dr in ([] if PACIFIST else obs.get("drops", [])):
            p = dr["pos"]
            d = math.hypot(p[0] - x, p[1] - y)
            holder = dr.get("holder")
            if holder is not None and holder != self.me and hpf < 0.65:
                continue
            if d > DROP_RANGE or not self.in_circle(p[0], p[1], zcx, zcy, zr, 10):
                continue
            if dr.get("lands_in", 0) > d / 11.0 + 6:
                continue
            danger = False
            nnear = 0
            for m in obs.get("mechs", []):
                if m["kind"] == "mech" and math.hypot(m["pos"][0] - p[0], m["pos"][1] - p[1]) < 60:
                    nnear += 1
                    mf_ = (m.get("hp", 1400) or 1) / max(1.0, m.get("max_hp", 1400) or 1400)
                    if mf_ > hpf * 0.9:
                        danger = True
            if nnear >= 2:
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
        # cubes (seen now or remembered)
        best = None
        cubes_all = list(obs.get("cubes", []))
        if FARM_ROAM:
            seen_ids = {c["id"] for c in cubes_all}
            cubes_all += [{"id": k, "pos": v} for k, v in self.known_cubes.items() if k not in seen_ids]
        for c in cubes_all:
            p = c["pos"]
            if not self.reachable_item(p) or not self.in_circle(p[0], p[1], zcx, zcy, zr, 10):
                continue
            if math.hypot(p[0] - x, p[1] - y) > CUBE_RANGE:
                continue
            d = math.hypot(p[0] - x, p[1] - y)
            if best is None or d < best[0]:
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
        if VULTURE and hpf > VULTURE_HP:
            g = self.vulture_goal(x, y, zcx, zcy, zr)
            if g is not None:
                return g
        if FARM_ROAM and t < FARM_UNTIL and hpf > FARM_HP:
            g = self.roam_goal(x, y, zone, zcx, zcy, zr)
            if g is not None:
                return g
        return None

    def listen(self, obs, x, y, t):
        """Turn fight / death sounds into estimated map points (bearing +- 7 deg, coarse range)."""
        for snd in obs.get("sounds", []):
            k = snd.get("kind")
            b = snd.get("bearing")
            if b is None:
                continue
            dist = SOUND_DIST.get(snd.get("dist"), 110.0)
            px, py = x + math.cos(b) * dist, y + math.sin(b) * dist
            ts = t - (snd.get("age") or 0.0)
            if k == "death" and snd.get("dist") in ("near", "mid"):
                self.death_sites.append((ts, px, py))
            elif k in FIGHT_SOUNDS and snd.get("dist") in ("near", "mid"):
                self.fight_snd.append((ts, px, py, snd.get("dist")))
        self.fight_snd = [f for f in self.fight_snd if t - f[0] < 6.0][-40:]
        self.death_sites = [d for d in self.death_sites if t - d[0] < 25.0][-8:]

    def vulture_goal(self, x, y, zcx, zcy, zr):
        t = self.t
        # a mech just died nearby: its cubes (all it had + 2) are lying there
        best = None
        for ts, px, py in self.death_sites:
            d = math.hypot(px - x, py - y)
            if d < 170 and self.in_circle(px, py, zcx, zcy, zr, 10) and (best is None or d < best[0]):
                best = (d, px, py)
        if best is not None:
            if best[0] < 8:
                self.death_sites = [s_ for s_ in self.death_sites if math.hypot(s_[1] - best[1], s_[2] - best[2]) > 8]
            else:
                self.vulture_until = t + 6.0
                return (best[1], best[2], "loot-death")
        # an ongoing fight: close in to a standoff distance and wait for a weakened survivor
        recent = [f for f in self.fight_snd if t - f[0] < 4.0]
        if len(recent) < 2:
            return None
        fx = sum(f[1] for f in recent) / len(recent)
        fy = sum(f[2] for f in recent) / len(recent)
        if not self.in_circle(fx, fy, zcx, zcy, zr, 20):
            return None
        d = math.hypot(fx - x, fy - y)
        self.vulture_until = t + 6.0
        if d <= VULTURE_STANDOFF + 10:
            return (x, y, "vulture")
        ux, uy = (fx - x) / d, (fy - y) / d
        return (fx - ux * VULTURE_STANDOFF, fy - uy * VULTURE_STANDOFF, "vulture")

    def remember_farm(self, obs, x, y, eye, t):
        kc = self.known_crates
        seen = set()
        for c in obs.get("crates", []):
            kc[c["id"]] = (c["pos"], t)
            seen.add(c["id"])
        for m in obs.get("mechs", []):
            if m.get("kind") == "npc":
                self.known_npcs[m["id"]] = (m["pos"], t)
        kq = self.known_cubes
        cseen = set()
        for c in obs.get("cubes", []):
            kq[c["id"]] = c["pos"]
            cseen.add(c["id"])
        for cid in list(kq.keys()):
            if cid in cseen:
                continue
            p = kq[cid]
            dd = math.hypot(p[0] - x, p[1] - y)
            if dd < 3.0 or (dd < 35 and self.nav.los(eye, (p[0], p[1], p[2] + 0.5), 1.0)):
                del kq[cid]  # picked up (by us or someone else)
        # forget crates that should be visible but aren't (destroyed)
        for cid in list(kc.keys()):
            if cid in seen:
                continue
            p = kc[cid][0]
            if math.hypot(p[0] - x, p[1] - y) < 40 and self.nav.los(eye, (p[0], p[1], p[2] + 1.2), 1.0):
                del kc[cid]
        for nid in list(self.known_npcs.keys()):
            if t - self.known_npcs[nid][1] > 45:
                del self.known_npcs[nid]
        for m in obs.get("events", []):
            if m.get("type") == "kill":
                self.known_npcs.pop(m.get("target"), None)

    def roam_goal(self, x, y, zone, zcx, zcy, zr):
        """Go to the nearest remembered crate / drone, else explore inside the zone to find some."""
        t = self.t
        nav = self.nav
        best = None
        for cid, (p, ts) in self.known_crates.items():
            if not self.in_circle(p[0], p[1], zcx, zcy, zr, 25) or p[2] - nav.ground(p[0], p[1]) > 2.5:
                continue
            d = math.hypot(p[0] - x, p[1] - y)
            if d < FARM_RANGE and (best is None or d < best[0]):
                best = (d, p, cid, "crate")
        for nid, (p, ts) in self.known_npcs.items():
            if not self.in_circle(p[0], p[1], zcx, zcy, zr, 25):
                continue
            d = math.hypot(p[0] - x, p[1] - y) - 25.0  # 2 cubes: worth a detour
            if d < FARM_RANGE and (best is None or d < best[0]):
                best = (d, p, nid, "npc")
        if best is not None:
            p = best[1]
            if math.hypot(p[0] - x, p[1] - y) < 6.0 and best[3] == "crate":
                self.known_crates.pop(best[2], None)  # got there, nothing to shoot: gone
                return None
            return (p[0], p[1], "seek")
        ep = self.explore_pt
        if ep is None or math.hypot(ep[0] - x, ep[1] - y) < 12 or t - self.explore_t > 25 or \
                not self.in_circle(ep[0], ep[1], zcx, zcy, zr, 40):
            nc = zone["next_center"]
            cands = []
            for _ in range(10):
                a = self.rng.uniform(-math.pi, math.pi)
                r = self.rng.uniform(70, 150)
                px, py = x + r * math.cos(a), y + r * math.sin(a)
                if not self.in_circle(px, py, zcx, zcy, zr, 45) or not nav.free(px, py):
                    continue
                cands.append((math.hypot(px - nc[0], py - nc[1]) + self.rng.uniform(0, 80), px, py))
            if not cands:
                return None
            cands.sort()
            self.explore_pt = (cands[0][1], cands[0][2])
            self.explore_t = t
            ep = self.explore_pt
        return (ep[0], ep[1], "explore")

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
