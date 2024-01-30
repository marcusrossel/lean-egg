#!/usr/bin/env python3
from __future__ import annotations
import tqdm
import subprocess
import resource
import itertools
import csv

filename = "ThreeGuided.lean"
guides_start = 25
guides_end = 30
num_runs = 10
warmup = 0


def powerset(n : int) -> list[bool]:
    #eager for simplicity
    return list(itertools.product([False, True], repeat=n))

def remove_guides(filename : str, guides_start : int, guides_end : int, guides_to_remove : list[bool]) -> str:
    assert( len(guides_to_remove) == guides_end - guides_start )
    res = ""
    with open(filename, "r") as f:
        for line, content in enumerate(f.readlines()):
            if line < guides_start or line >= guides_end:
                res += content
            else:
                if guides_to_remove[line - guides_start]:
                    continue
                else:
                    res += content
    return res


def benchmark_subset(warmup : int, num_runs : int, filename : str, guides_start : int, guides_end : int, guides_to_remove : list[bool]) -> list[dict]:
    res = []
    print(f"Running {guides_to_remove}... (warmup)")
    with open("PowerSetTest.lean", "w") as f:
        removed = remove_guides(filename, guides_start, guides_end, guides_to_remove)
        f.write(removed)
    for _ in tqdm.tqdm(range(warmup)):
        subprocess.run(f"./measure.py PowerSetTest", shell=True)
    print(f"Benchmarking...")
    for _ in tqdm.tqdm(range(num_runs)):
        start = resource.getrusage(resource.RUSAGE_CHILDREN)
        #TODO: currently measure.py is not returning an error if it kills just egg the subprocess
        subprocess.run(f"./measure.py PowerSetTest", shell=True)
        end = resource.getrusage(resource.RUSAGE_CHILDREN)
        res.append({ 'time' : end.ru_utime - start.ru_utime, 'mem' : end.ru_maxrss - start.ru_maxrss, 'guides' : guides_to_remove })
    return res

def main():
    with open('results_powerset.csv', 'w') as f:
        csv_writer = csv.writer(f)
        csv_writer.writerow(["Test", "Time", "Memory", "Guides"])
        for guides in powerset(guides_end - guides_start):
            res = benchmark_subset(warmup, num_runs, filename, guides_start, guides_end, guides)
            for r in res:
                csv_writer.writerow([filename, r['time'], r['mem'], r['guides']])

if __name__ == "__main__":
    main()
