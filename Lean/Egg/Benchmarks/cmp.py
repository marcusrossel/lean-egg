#!/usr/bin/python3 -B

import sys

detour_lines = open("detour").readlines()
original_lines = open("original").readlines()

GREEN = "\033[32m"
RED = "\033[31m"
RESET = "\033[0m"

greens = 0
reds = 0

def gt(x, y):
    try:
        return int(x) > int(y)
    except Exception:
        return False

i = int(sys.argv[1])
print(detour_lines[0].split(",")[i])
for l, r in zip(detour_lines[1:], original_lines[1:]):
    ex = l.split(",")[0]

    l = l.split(",")[i]
    r = r.split(",")[i]
    color = RESET
    op = " "
    if gt(l, r) :
        reds += 1
        color = RED
        op = ">"
    elif gt(r, l):
        greens += 1
        color = GREEN
        op = "<"
    print(f"{color}{ex:32} D: {l:6} {op} O: {r:6}{RESET}")
print(f"GREENS: {greens} / REDS: {reds}")
