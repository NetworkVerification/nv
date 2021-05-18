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
from typing import Any, Optional

# constants for mean_float_dict's handling of operations that run multiple
# times across partitions
# produce an int total of the time each operation took
SUM_OPERATIONS = 0
# produce a list of the time each operation took (default)
LIST_OPERATIONS = 1
# produce separate keys to distinguish each operation's time taken
DISTINCT_OPERATIONS = 2


def fill_matrix(matrix: list[list[int]]):
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


def mean_float_dict(dicts: list[dict], multiop=LIST_OPERATIONS) -> dict:
    """
    Average the results across the given list of dictionaries.
    The multiop flag determines what to do in cases where an operation
    occurs multiple times in a single run, e.g. inlining.
    """
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
        if multiop == LIST_OPERATIONS:
            averaged[key] = newval
        elif multiop == SUM_OPERATIONS:
            averaged[key] = sum(newval)
        elif multiop == DISTINCT_OPERATIONS:
            for (i, val) in enumerate(newval):
                averaged[key + " " + str(i)] = val
        else:
            raise NotImplementedError()
    return averaged


def join_result_dicts(
    *dicts: tuple[str, Optional[str], dict[str, Any]]
) -> tuple[str, dict[str, Any]]:
    """
    Join the results dictionaries for separate cuts into a single dictionary over all cuts.
    """
    joined = dict()
    logs = ""
    for (log, cut, results) in dicts:
        for (key, val) in results.items():
            if cut is None:
                cut = "monolithic"
            joined[key + f" ({cut})"] = val
        logs += log
    return logs, joined


def parse_smt(output: str) -> dict:
    """
    Parse the output of an NV command.
    Returns a dictionary of strings to lists of floats.
    """
    action = re.compile(r"(.*) took: (\d*\.?\d+) secs to complete", re.M)
    z3action = re.compile(r"^\s*:(\w*)\s*(\d*\.?\d+)", re.M)
    assertion = re.compile(r"(Assertion|Guarantee) (\d*) failed", re.M)
    profile = dict()
    # get transformation profiling
    for match in action.finditer(output):
        transform = match.group(1)
        time = float(match.group(2))
        profile.setdefault(transform, list()).append(time)
    # get z3 profiling
    for match in z3action.finditer(output):
        stat = "z3 " + match.group(1)
        qua = float(match.group(2))
        profile.setdefault(stat, list()).append(qua)
    # get assertion failures
    for match in assertion.finditer(output):
        assn = match.group(2)
        profile.setdefault("failed", list()).append(assn)
    return profile


def run_nv_smt(path: str, cut: Optional[str], time: float, verbose: bool):
    """
    Run nv's SMT tool and capture its output.
    If it doesn't finish within the given time, kill it.
    """
    log = ""
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
    log += f"Running {' '.join(args)}\n"
    try:
        proc = subprocess.run(
            args, text=True, check=True, capture_output=True, timeout=time
        )
        if verbose:
            log += proc.stdout + "\n"
        return log, parse_smt(proc.stdout)
    except subprocess.CalledProcessError as exn:
        if verbose:
            log += exn.stdout + "\n"
        log += f"Error: {exn}\n"
        return log, {}
    except subprocess.TimeoutExpired as exn:
        if verbose:
            log += exn.stdout + "\n"
        log += f"Timeout after {exn.timeout} seconds: {exn}\n"
        return log, {}


def run_bench(cut, path, time, verbose):
    log, result = run_nv_smt(path, cut, time, verbose)
    return (log, cut, result)


def run_benchmarks_sync(benchdir, benches, time, verbose) -> tuple[str, dict]:
    """
    Run the given benchmarks in the given directory in sequence (once each).
    Return a log of output and a dictionary with the benchmark results for each cut.
    """
    return join_result_dicts(
        *[run_bench(c, os.path.join(benchdir, n), time, verbose) for (c, n) in benches]
    )


def run_benchmarks_parallel(benchdir, benches, time, verbose) -> tuple[str, dict]:
    """
    Run the given benchmarks in the given directory in parallel (once each).
    Return a log of output and a dictionary with the benchmark results for each cut.
    """
    # set up the args for each run_bench
    paths = map(lambda t: (t[0], os.path.join(benchdir, t[1]), time, verbose), benches)

    with multiprocessing.Pool(processes=len(benches)) as pool:
        return join_result_dicts(
            *pool.starmap(
                run_bench,
                paths,
            )
        )


def run_trials_sync(benchdir, benches, time, trials, multiop, verbose, average):
    """
    Run trials of the given benchmarks and return a dictionary of profiling information.
    """
    runs = []
    log = ""
    for i in range(trials):
        log += "Running trial " + str(i + 1) + " of " + str(trials) + "\n"
        logs, results = run_benchmarks_sync(benchdir, benches, time, verbose)
        log += logs
        runs.append(results)
    if average:
        mean = mean_float_dict(runs, multiop)
        mean["Benchmark"] = benchdir
    else:
        mean = runs
    return log, mean


def run_trials_parallel(benchdir, benches, time, trials, multiop, verbose, average):
    """
    Run the benchmarks in the given directory and return a dictionary of
    profiling information.
    Runs each trial in parallel.
    """
    with multiprocessing.Pool(processes=trials) as pool:
        args = [(benchdir, benches, time, verbose) for _ in range(trials)]
        runs = pool.starmap(run_benchmarks_sync, args)
        logs, results = map(list, zip(*runs))
        if average:
            mean = mean_float_dict(results, multiop)
            mean["Benchmark"] = benchdir
        else:
            mean = results
        log = "".join(logs)
        return log, mean


def write_csv(results: dict[int, list[dict]], path):
    """
    Write the results dictionary to a CSV.
    Each line of the CSV describes an operation run for a given cut during a given trial,
    some number of times (some operations may run many times if the cut produces many subnetworks).
    """
    # get all field names
    fields = set()
    for result in results.values():
        fields.update(set([r.keys() for r in result]))
    with open(path, "w") as csvf:
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
        RUNS.append(
            run_trials_sync(
                benchdir, benchmarks, TIMEOUT, TRIALS, OP, verbose=False, average=True
            )
        )
    write_csv(RUNS, "kirigami-results-test.csv")
