#!/usr/bin/python3
"""
Compute benchmark results comparing partitioned and unpartitioned SMT checks.
"""
import multiprocessing
import subprocess
import os
import sys
import re
import csv

# constants for mean_float_dict's handling of operations that run multiple
# times across partitions
# produce an int total of the time each operation took
SUM_OPERATIONS = 0
# produce a list of the time each operation took (default)
LIST_OPERATIONS = 1
# produce separate keys to distinguish each operation's time taken
DISTINCT_OPERATIONS = 2


def fill_matrix(matrix):
    """
    Return a new list of lists (matrix) where inner lists all have the same
    length. Inner lists that are short elements have the element 0 added.
    """
    result = []
    lengths = [len(row) for row in matrix]
    maxlen = max(lengths)
    for (i, row) in enumerate(matrix):
        if lengths[i] < maxlen:
            pad = [0] * (maxlen - lengths[i])
        else:
            pad = []
        result.append(row + pad)
    return result


def mean_float_dict(dicts, multiop=LIST_OPERATIONS):
    """
    Average the results across the given list of dictionaries.
    """
    if len(dicts) == 0:
        return []
    averaged = dict()
    keys = set()
    for d in dicts:
        keys.update(set(d.keys()))
    for key in keys:
        try:
            vals = [d[key] for d in dicts]
            # fill in missing columns
            corrected = fill_matrix(vals)
            newval = [sum(x) / len(dicts) for x in zip(*corrected)]
        except KeyError:
            # skip any key that is missing from a dictionary
            continue
        except IndexError:
            print(key)
            print([d[key] for d in dicts])
            sys.exit(1)
        # if total is true, sum all the parts together
        if multiop == LIST_OPERATIONS:
            averaged[key] = newval
        elif multiop == SUM_OPERATIONS:
            averaged[key] = sum(newval)
        # otherwise, just return a list of each time that
        # operation was profiled
        elif multiop == DISTINCT_OPERATIONS:
            for (i, val) in enumerate(newval):
                averaged[key + " " + str(i)] = val
        else:
            raise NotImplementedError()
    return averaged


def join_result_dicts(*dicts):
    """
    Join the results dictionaries into a single dictionary.
    """
    joined = dict()
    for (cut, results) in dicts:
        for (key, val) in results.items():
            if cut is None:
                cut = "monolithic"
            joined[key + f" ({cut})"] = val
    return joined


def parse_smt(output):
    """
    Parse the output of an NV command.
    Returns a dictionary of strings to lists of floats.
    """
    action = re.compile(r"(.*) took: (\d*\.?\d+) secs to complete", re.M)
    z3action = re.compile(r"^\s*:(\w*)\s*(\d*\.?\d+)", re.M)
    # get all the transformation profiling
    profile = dict()
    if "failed" in output:
        print("WARNING: assertions failed during verification!")
        profile["safe"] = False
    else:
        profile["safe"] = True
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


def run_nv_smt(path, cut, time):
    """
    Run nv's SMT tool and capture its output.
    If it doesn't finish within the given time, kill it.
    """
    nvpath = os.path.join(os.getcwd(), "nv")
    if not os.path.exists(nvpath):
        print("Did not find 'nv' executable in the current working directory")
        sys.exit(1)
    # set verbose, SMT flags, and partitioning if needed
    args = [nvpath, "-v", "-m"]
    if cut is not None:
        args += ["-k", path]
    else:
        args += [path]
    print(f"Running {' '.join(args)}")
    try:
        proc = subprocess.run(
            args, text=True, check=True, capture_output=True, timeout=time
        )
        return parse_smt(proc.stdout)
    except subprocess.CalledProcessError as exn:
        print(exn.stderr)
        return {}
    except subprocess.TimeoutExpired as exn:
        print(exn.stderr)
        return {}


def run_bench(cut, path, time):
    return (cut, run_nv_smt(path, cut, time))


def run_benchmarks_sync(benchdir, benches, time):
    """
    Run the given benchmarks in the given directory in sequence.
    """
    return join_result_dicts(
        *[run_bench(c, os.path.join(benchdir, n), time) for (c, n) in benches]
    )


def run_benchmarks_parallel(benchdir, benches, time):
    """
    Run the given benchmarks in the given directory in parallel.
    """
    paths = map(lambda t: (t[0], os.path.join(benchdir, t[1]), time), benches)

    with multiprocessing.Pool(processes=len(benches)) as pool:
        return join_result_dicts(
            *pool.starmap(
                run_bench,
                paths,
            )
        )


def run_trials_sync(benchdir, benches, time, trials, multiop):
    """
    Run trials of the given benchmarks
    and return a dictionary of profiling information.
    """
    runs = []
    for i in range(trials):
        print("Running trial " + str(i + 1) + " of " + str(trials))
        results = run_benchmarks_sync(benchdir, benches, time)
        runs.append(results)
    mean = mean_float_dict(runs, multiop)
    mean["Benchmark"] = benchdir
    return mean


def run_trials_parallel(benchdir, benches, time, trials, multiop):
    """
    Run the benchmarks in the given directory and return a dictionary of
    profiling information.
    Runs each trial in parallel.
    """
    with multiprocessing.Pool(processes=trials) as pool:
        args = [(benchdir, benches, time) for _ in range(trials)]
        runs = pool.starmap(run_benchmarks_sync, args)
        mean = mean_float_dict(runs, multiop)
        mean["Benchmark"] = benchdir
        return mean


def write_csv(results, path):
    """Write the results dictionaries to a CSV."""
    # get all field names
    fields = set()
    for result in results:
        fields.update(set(result.keys()))
    with open(path, "w") as csvf:
        # use the last results, which will have the most keys
        writer = csv.DictWriter(csvf, fieldnames=list(fields), restval="")
        writer.writeheader()
        for result in results:
            writer.writerow(result)


if __name__ == "__main__":
    DIRECTORY = "benchmarks/SinglePrefix/FAT{}"
    SIZES = [4, 8]
    TIMEOUT = 3600
    TRIALS = 10
    RUNS = []
    OP = DISTINCT_OPERATIONS
    for sz in SIZES:
        benchdir = DIRECTORY.format(sz)
        print(f"Running benchmark {benchdir}")
        benchmarks = [
            (None, f"sp{sz}.nv"),
            ("horizontal", f"sp{sz}-part.nv"),
            ("vertical", f"sp{sz}-vpart.nv"),
            ("pods", f"sp{sz}-pods.nv"),
        ]
        RUNS.append(run_trials_sync(benchdir, benchmarks, TIMEOUT, TRIALS, OP))
    write_csv(RUNS, "kirigami-results-test.csv")
