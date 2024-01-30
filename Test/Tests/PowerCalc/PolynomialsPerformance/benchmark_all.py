#!/usr/bin/env python3
import tqdm
import subprocess
import resource
import csv

tests = ["TwoGuided", "TwoManual", "TwoUnguided", "TwoBaselineEgg"]
num_runs = 10
warmup = 2

def benchmark_test(test, warmup, num_runs):
  res = []
  print(f"Running {test}... (warmup)")
  for _ in tqdm.tqdm(range(warmup)):
      subprocess.run(f"./measure.py {test}", shell=True)
  print(f"Benchmarking {test}...")
  for _ in tqdm.tqdm(range(num_runs)):
    start = resource.getrusage(resource.RUSAGE_CHILDREN)
    #TODO: currently measure.py is not returning an error if it kills just egg the subprocess
    subprocess.run(f"./measure.py {test}", shell=True)
    end = resource.getrusage(resource.RUSAGE_CHILDREN)
    res.append({ 'time' : end.ru_utime - start.ru_utime, 'mem' : end.ru_maxrss - start.ru_maxrss})
  return res

def main():
    with open('results.csv', 'w') as f:
        csv_writer = csv.writer(f)
        csv_writer.writerow(["Test", "Time", "Memory", "Timeout"])
        for t in tests:
            res = benchmark_test(t, warmup, num_runs)
            for r in res:
                csv_writer.writerow([t, r['time'], r['mem']]) #, r['timeout']])

if __name__ == "__main__":
    main()
