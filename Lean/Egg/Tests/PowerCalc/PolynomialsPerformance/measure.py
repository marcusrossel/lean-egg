#!/usr/bin/env python3
import subprocess
import resource
from sys import argv

time_limit = 60 #minutes
mem_limit = 8 #GB

def run_test(test):
    resource.setrlimit(resource.RLIMIT_AS, (gb_to_b(mem_limit) - 1, gb_to_b(mem_limit)))
    resource.setrlimit(resource.RLIMIT_CPU, (min_to_sec(time_limit) - 1, min_to_sec(time_limit)))
    cmd = f"(cd ../../../; lake build PowerCalc.Examples.PolynomialsPerformance.{test})"
    res = subprocess.run(cmd, shell=True, capture_output=True)
    return res

def gb_to_b(b):
    return int(b * 1024 * 1024 * 1024)

def min_to_sec(m):
    return int(m * 60)

if __name__ == "__main__":
    if len(argv) != 2:
        print("Usage: ./measure.py <test>")
        exit(1)
    filename = argv[1]
    run_test(filename)
