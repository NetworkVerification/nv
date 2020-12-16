#!/usr/bin/python3
"""
Compute benchmark results comparing partitioned and unpartitioned SMT checks.
"""
import subprocess
import os
import sys
import re
import csv

# constants for mean_float_dict's handling of operations that run multiple times across partitions
# produce an int total of the time each operation took
SUM_OPERATIONS = 0
# produce a list of the time each operation took (default)
LIST_OPERATIONS = 1
# produce separate keys to distinguish each operation's time taken
DISTINCT_OPERATIONS = 2


def mean_float_dict(dicts, multiop=LIST_OPERATIONS):
    """
    Average the results across the given list of dictionaries.
    """
    if len(dicts) == 0:
        return []
    averaged = dict()
    keys = dicts[0].keys()
    for key in keys:
        newval = []
        try:
            for i in range(len(dicts[0][key])):
                sumval = sum([d[key][i] for d in dicts])
                newval.append(sumval / len(dicts))
        except KeyError:
            # skip any key that is missing from a dictionary
            continue
        # if total is true, sum all the parts together
        if multiop == LIST_OPERATIONS:
            averaged[key] = newval
        elif multiop == SUM_OPERATIONS:
            averaged[key] = sum(newval)
        # otherwise, just return a list of each time that operation was profiled
        elif multiop == DISTINCT_OPERATIONS:
            for (i, nv) in enumerate(newval):
                averaged[key + " " + str(i)] = nv
        else:
            raise NotImplemented()
    return averaged


def join_result_dicts(parted, vparted, unparted):
    """
    Join the three dictionaries representing two partitioned runs and an unpartitioned run
    into a single dictionary.
    """
    joined = dict()
    for (key, val) in parted.items():
        joined[key + " (part)"] = val
    for (key, val) in vparted.items():
        joined[key + " (vpart)"] = val
    joined.update(unparted)
    return joined


def parse_output(output):
    """
    Parse the output of an NV command.
    Returns a dictionary of strings to lists of floats.
    """
    action = re.compile(r"(.*) took: (\d*\.?\d+) secs to complete", re.M)
    z3action = re.compile(r"^\s*:(\w*)\s*(\d*\.?\d+)", re.M)
    # get all the transformation profiling
    profile = dict()
    for match in re.finditer(action, output):
        transform = match.group(1)
        time = float(match.group(2))
        profile.setdefault(transform, list()).append(time)
    # get all the z3 profiling
    for match in re.finditer(z3action, output):
        stat = "z3 " + match.group(1)
        qua = float(match.group(2))
        profile.setdefault(stat, list()).append(qua)
    return profile


def run_command(com, time):
    """
    Run the given command and capture its output.
    If it doesn't finish within the given time, kill it.
    """
    try:
        proc = subprocess.run(
            com, text=True, check=True, capture_output=True, timeout=time
        )
        return parse_output(proc.stdout)
    except subprocess.CalledProcessError as exn:
        print(exn.stderr)
        return {}
    except subprocess.TimeoutExpired as exn:
        print(exn.stderr)
        return {}


def run_benchmark(dirformat, nameformat, size, time, trials, multiop):
    """
    Run the partitioned and unpartitioned benchmarks in the given directory,
    and return a dictionary of profiling information.
    """
    benchdir = dirformat.format(size)
    nvpath = os.path.join(os.getcwd(), "nv")
    if not os.path.exists(nvpath):
        print("Did not find an 'nv' executable in the current working directory!")
        sys.exit(1)
    # run nv with verbose, SMT and partitioning flags
    com = [nvpath, "-v", "-m"]
    partf = os.path.join(benchdir, nameformat.format(size, "-part"))
    vpartf = os.path.join(benchdir, nameformat.format(size, "-vpart"))
    unpartf = os.path.join(benchdir, nameformat.format(size, ""))
    runs = []
    for i in range(trials):
        print("Running trial " + str(i + 1) + " of " + str(trials))
        partcom = run_command(com + ["-k", partf], time)
        vpartcom = run_command(com + ["-k", vpartf], time)
        unpartcom = run_command(com + [unpartf], time)
        runs.append(join_result_dicts(partcom, vpartcom, unpartcom))
    mean = mean_float_dict(runs, multiop)
    mean["Benchmark"] = benchdir
    return mean


def write_csv(results, path):
    """Write the results dictionaries to a CSV."""
    with open(path, "w") as csvf:
        writer = csv.DictWriter(csvf, fieldnames=results[0].keys(), restval="error")
        writer.writeheader()
        for result in results:
            writer.writerow(result)


if __name__ == "__main__":
    DIRECTORY = "benchmarks/SinglePrefix/FAT{}"
    SIZES = [4, 8]
    TIMEOUT = 3600
    TRIALS = 10
    RUNS = []
    MULTIOP = DISTINCT_OPERATIONS
    for sz in SIZES:
        print("Running benchmark " + DIRECTORY.format(sz))
        RUNS.append(run_benchmark(DIRECTORY, "sp{}{}.nv", sz, TIMEOUT, TRIALS, MULTIOP))
    write_csv(RUNS, "kirigami-results-h1.csv")
