"""Offline: build the navigation / line-of-sight grid from the static map.

    python tools/build_nav.py <arena_dir> nav.bin

The map is identical every match, so the result is committed next to the bot.

nav.bin = zlib( header(json, \n) + blocked[u8 * N] + top[i16 * N] + base[i16 * N] + surf[i16 * N] )
  blocked: 0 free, 1 near a wall (inflated), 2 wall / impassable terrain
  top/base: highest top / lowest base (decimeters) of solids whose footprint covers the cell centre
            (base=top=-32768 when none); used for line of sight
  surf: walkable surface height at the cell centre (decimeters): terrain, or a low bridge deck
  otop: height (decimeters) to clear to get onto the cell (roof top / highest terrain sample)
"""
import array
import json
import math
import os
import sys
import zlib

CELL = 2.0
STEP_UP = 1.2
HEAD = 9.0
MAX_DH_PER_M = math.tan(math.radians(50.0))


def pip(x, y, ring):
    n = len(ring) // 2
    inside = False
    j = n - 1
    for i in range(n):
        xi, yi = ring[2 * i], ring[2 * i + 1]
        xj, yj = ring[2 * j], ring[2 * j + 1]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / (yj - yi) + xi:
            inside = not inside
        j = i
    return inside


def in_prism(x, y, p):
    if not pip(x, y, p["ring"]):
        return False
    for h in p.get("holes") or []:
        if h and pip(x, y, h):
            return False
    return True


def main(arena, out):
    w = json.load(open(os.path.join(arena, "v2", "world.json")))
    t = w["terrain"]
    tnx, tny, tminx, tminy, tstep = t["nx"], t["ny"], t["minX"], t["minY"], t["step"]
    ter = array.array("h")
    ter.frombytes(open(os.path.join(arena, "v2", "terrain.i16"), "rb").read())
    if sys.byteorder != "little":
        ter.byteswap()
    surf1 = [v * 0.01 for v in ter]  # 1 m sample surface

    def tz(x, y):
        fx = (x - tminx) / tstep
        fy = (y - tminy) / tstep
        i = max(0, min(tnx - 2, int(fx)))
        j = max(0, min(tny - 2, int(fy)))
        ax, ay = fx - i, fy - j
        k = j * tnx + i
        a = ter[k] * (1 - ax) + ter[k + 1] * ax
        b = ter[k + tnx] * (1 - ax) + ter[k + tnx + 1] * ax
        return (a * (1 - ay) + b * ay) * 0.01

    prisms = w["prisms"]
    # low bridges are walkable decks: raise the 1 m surface there
    for p in prisms:
        r = p["ring"]
        xs, ys = r[0::2], r[1::2]
        x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
        if p["kind"] != "bridge":
            continue
        for j in range(max(0, int((y0 - tminy) / tstep)), min(tny, int((y1 - tminy) / tstep) + 2)):
            for i in range(max(0, int((x0 - tminx) / tstep)), min(tnx, int((x1 - tminx) / tstep) + 2)):
                x, y = tminx + i * tstep, tminy + j * tstep
                g = ter[j * tnx + i] * 0.01
                if p["base"] - g < HEAD and in_prism(x, y, p):
                    surf1[j * tnx + i] = max(g, p["top"])

    # rough samples: neighbour height jump steeper than max slope
    rough = bytearray(tnx * tny)
    lim = MAX_DH_PER_M * tstep
    for j in range(tny):
        row = j * tnx
        for i in range(tnx):
            k = row + i
            h = surf1[k]
            if i + 1 < tnx and abs(surf1[k + 1] - h) > lim:
                rough[k] = 1
                rough[k + 1] = 1
            if j + 1 < tny and abs(surf1[k + tnx] - h) > lim:
                rough[k] = 1
                rough[k + tnx] = 1

    nx = int((tnx - 1) * tstep / CELL)
    ny = int((tny - 1) * tstep / CELL)
    N = nx * ny
    minx, miny = tminx, tminy
    blocked = bytearray(N)
    top = array.array("h", [-32768]) * N
    base = array.array("h", [-32768]) * N
    surf = array.array("h", [0]) * N
    otop = array.array("h", [0]) * N  # height a mech must clear to stand on / cross the cell

    per = int(CELL / tstep)
    for j in range(ny):
        for i in range(nx):
            c = j * nx + i
            # surface at centre (nearest 1m sample block)
            si, sj = i * per, j * per
            vals = [surf1[(sj + b) * tnx + si + a] for b in range(per + 1) for a in range(per + 1)]
            surf[c] = int(round(sum(vals) / len(vals) * 10))
            otop[c] = int(round(max(vals) * 10))
            if any(rough[(sj + b) * tnx + si + a] for b in range(per + 1) for a in range(per + 1)):
                blocked[c] = 2
            if i == 0 or j == 0 or i == nx - 1 or j == ny - 1:
                blocked[c] = 2

    for p in prisms:
        r = p["ring"]
        xs, ys = r[0::2], r[1::2]
        x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
        i0 = max(0, int((x0 - minx) / CELL) - 1)
        i1 = min(nx - 1, int((x1 - minx) / CELL) + 1)
        j0 = max(0, int((y0 - miny) / CELL) - 1)
        j1 = min(ny - 1, int((y1 - miny) / CELL) + 1)
        pt, pb = int(round(p["top"] * 10)), int(round(p["base"] * 10))
        for j in range(j0, j1 + 1):
            cy = miny + (j + 0.5) * CELL
            for i in range(i0, i1 + 1):
                cx = minx + (i + 0.5) * CELL
                if not in_prism(cx, cy, p):
                    continue
                c = j * nx + i
                top[c] = max(top[c], pt)
                base[c] = pb if base[c] == -32768 else min(base[c], pb)
                g = tz(cx, cy)
                if p["kind"] == "bridge":
                    if p["base"] - g >= HEAD:
                        continue  # walk under
                    # deck: walkable, surface already raised
                    blocked[c] = 0 if blocked[c] != 2 or p["top"] > g else blocked[c]
                    surf[c] = max(surf[c], pt)
                    continue
                if p["top"] - g > STEP_UP and p["base"] - g < HEAD:
                    blocked[c] = 2
                    otop[c] = max(otop[c], pt)

    # inflate walls by one cell (mech radius 2.5 m on a 2 m grid)
    inf = bytearray(blocked)
    for j in range(ny):
        for i in range(nx):
            c = j * nx + i
            if blocked[c] != 2:
                continue
            for dj in (-1, 0, 1):
                for di in (-1, 0, 1):
                    a, b = i + di, j + dj
                    if 0 <= a < nx and 0 <= b < ny and inf[b * nx + a] == 0:
                        inf[b * nx + a] = 1

    hdr = json.dumps({"nx": nx, "ny": ny, "minX": minx, "minY": miny, "cell": CELL}).encode() + b"\n"
    data = hdr + bytes(inf) + top.tobytes() + base.tobytes() + surf.tobytes() + otop.tobytes()
    open(out, "wb").write(zlib.compress(data, 9))
    print("cells", N, "walls", sum(1 for v in blocked if v == 2), "inflated", sum(1 for v in inf if v), "bytes", os.path.getsize(out))
    # ascii preview (every 4th cell)
    lines = []
    for j in range(ny - 1, -1, -6):
        lines.append("".join("#" if inf[j * nx + i] == 2 else ("+" if inf[j * nx + i] else ".") for i in range(0, nx, 3)))
    open(out + ".txt", "w").write("\n".join(lines))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
