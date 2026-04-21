#!/usr/bin/python3 -B

import sys

detour_lines = open(sys.argv[2]).readlines()
original_lines = open(sys.argv[3]).readlines()

GREEN = "\033[32m"
RED = "\033[31m"
RESET = "\033[0m"

greens = 0
reds = 0
whites = 0

WHITE_DELTA = 10

def cmp(x, y):
    try:
        x = int(x)
        y = int(y)
    except Exception:
        return 0

    if abs(x-y) < WHITE_DELTA: return 0
    if x < y: return 1
    if x > y: return -1

i = int(sys.argv[1])
print(detour_lines[0].split(",")[i])
for l, r in zip(detour_lines[1:], original_lines[1:]):
    ex = l.split(",")[0]

    l = l.split(",")[i]
    r = r.split(",")[i]
    color = RESET
    op = " "
    c = cmp(l, r)
    if c == -1:
        reds += 1
        color = RED
        op = ">"
    elif c == 0:
        whites += 1
        color = RESET
        op = "~"
    else:
        greens += 1
        color = GREEN
        op = "<"
    print(f"{color}{ex:32} D: {l:6} {op} O: {r:6}{RESET}")
print(f"GREENS: {greens} / REDS: {reds} / WHITES: {whites}")
