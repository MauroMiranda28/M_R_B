"""Offline: exposure map of the arena (how open each spot is to fire from around it).

    python tools/build_cover.py            # writes cover.bin next to bot.py

For each 4 m cell: cast 16 horizontal rays at eye height (ground + 6 m) against buildings and terrain
(the 2 m nav raster; trees ignored because shots go through them) and average min(clear distance, 120 m)/120.
0 = enclosed (an alcove, a courtyard corner), 255 = open field. Walls / unreachable cells get 255.

cover.bin = zlib( json header \n + u8 * (nx * ny) )
"""
import json
import math
import multiprocessing as mp
import os
import sys
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

CELL = 4.0
DIRS = 16
RMAX = 120.0
STEP = 2.0
EYE = 6.0

_nav = None


def nav():
    global _nav
    if _nav is None:
        import bot
        _nav = bot.Nav(os.path.join(ROOT, "nav.bin"))
    return _nav


def row(j):
    n = nav()
    nx = int(n.nx * n.cell / CELL)
    out = bytearray(nx)
    top, base, surf, blk = n.top, n.base, n.surf, n.blk
    inv, gnx, gny = n.inv, n.nx, n.ny
    dirs = [(math.cos(k * 2 * math.pi / DIRS), math.sin(k * 2 * math.pi / DIRS)) for k in range(DIRS)]
    steps = int(RMAX / STEP)
    for i in range(nx):
        x = n.minx + (i + 0.5) * CELL
        y = n.miny + (j + 0.5) * CELL
        c0 = n.idx(x, y)
        if blk[c0] != 0:
            out[i] = 255
            continue
        z = (surf[c0] * 0.1 + EYE) * 10.0   # decimetres, like the raster
        tot = 0.0
        for dx, dy in dirs:
            clear = RMAX
            for k in range(1, steps + 1):
                px, py = x + dx * k * STEP, y + dy * k * STEP
                gi, gj = int((px - n.minx) * inv), int((py - n.miny) * inv)
                if gi < 0 or gj < 0 or gi >= gnx or gj >= gny:
                    break
                c = gj * gnx + gi
                t = top[c]
                if (t != -32768 and base[c] - 5 <= z <= t) or surf[c] > z + 3:
                    clear = k * STEP
                    break
            tot += clear / RMAX
        out[i] = int(round(255 * tot / DIRS))
    return j, bytes(out)


def main():
    n = nav()
    nx = int(n.nx * n.cell / CELL)
    ny = int(n.ny * n.cell / CELL)
    rows = [None] * ny
    with mp.Pool(max(1, (os.cpu_count() or 2) - 2)) as pool:
        for j, r in pool.imap_unordered(row, range(ny)):
            rows[j] = r
    data = b"".join(rows)
    hdr = json.dumps({"nx": nx, "ny": ny, "minX": n.minx, "minY": n.miny, "cell": CELL, "dirs": DIRS, "rmax": RMAX}).encode() + b"\n"
    out = os.path.join(ROOT, "cover.bin")
    open(out, "wb").write(zlib.compress(hdr + data, 9))
    free = [v for v in data if v < 255]
    free.sort()
    print(f"{nx}x{ny} cells, file {os.path.getsize(out)} bytes; free cells {len(free)}; exposure quantiles 10/50/90:",
          [round(free[int(len(free) * q)] / 255, 2) for q in (0.1, 0.5, 0.9)])


if __name__ == "__main__":
    main()
