"""Offline: find low-exposure, climbable roof spots and save them for the bot.

    python tools/roof_spots.py nav.bin roofspots.json

A spot is the interior of a flat roof (all cells within 8 m on the same roof), 8-45 m above the street.
Exposure = fraction of open-ground eyes (z+8) 30-200 m away that can see the mech's centre or top.
"""
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import bot as B  # noqa: E402

DIRS, DISTS = 24, (30, 60, 100, 150, 200)


def main(nav_path, out):
    nav = B.Nav(nav_path)
    nx = nav.nx

    def exposure(x, y, zf):
        seen = tot = 0
        for k in range(DIRS):
            a = k * 2 * math.pi / DIRS
            for d in DISTS:
                ex, ey = x + d * math.cos(a), y + d * math.sin(a)
                c = nav.idx(ex, ey)
                if nav.blk[c] != 0:
                    continue
                tot += 1
                eye = (ex, ey, nav.surf[c] * 0.1 + 8.0)
                if nav.los(eye, (x, y, zf + 4.5), 0.5) or nav.los(eye, (x, y, zf + 9.0), 0.5):
                    seen += 1
        return seen / max(1, tot), tot

    def interior(c, h, r=4):
        i0, j0 = c % nx, c // nx
        for dj in range(-r, r + 1):
            for di in range(-r, r + 1):
                cc = (j0 + dj) * nx + i0 + di
                if cc < 0 or cc >= len(nav.blk) or nav.blk[cc] != 2 or abs(nav.stand[cc] - h) > 1.5:
                    return False
        return True

    spots = []
    step = 3  # cells (6 m)
    for j in range(5, nav.ny - 5, step):
        for i in range(5, nx - 5, step):
            c = j * nx + i
            if nav.blk[c] != 2 or nav.top[c] == B.UNSET:
                continue
            h = nav.stand[c]
            rise = h - nav.surf[c] * 0.1
            if not (8.0 <= rise <= 45.0) or not interior(c, h):
                continue
            x, y = nav.center(c)
            e, n = exposure(x, y, h)
            if n >= 30 and e <= 0.55:
                spots.append([round(x, 1), round(y, 1), round(h, 2), round(e, 3), round(rise, 1)])
    spots.sort(key=lambda s: s[3])
    json.dump({"spots": spots}, open(out, "w"), separators=(",", ":"))
    print(len(spots), "spots; best", spots[:5])


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
