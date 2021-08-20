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


def join_cut_dicts(
    *dicts: tuple[str, Optional[str], dict[str, Any]]
) -> tuple[str, dict[str, dict[str, Any]]]:
    """
    Join the results dictionaries for separate cuts into a single dictionary over all cuts.
    """
    joined = dict()
    logs = ""
    for (log, cut, results) in dicts:
        if cut is None:
            cut = "monolithic"
        joined[cut] = results
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
    z3timeout = re.compile(r"Z3 timed out after (\d*)", re.M)
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
    # get z3 timeouts
    for match in z3timeout.finditer(output):
        time = int(match.group(1))
        profile.setdefault("z3 timeout", list()).append(time)
    return profile


def run_nv_smt(path: str, cut: Optional[str], z3time: int, time: float, verbose: bool):
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
    args = [nvpath, "-v", "-m", "-t", str(z3time)]
    if cut is not None:
        args += ["-k", path]
    else:
        args += [path]
    log += f"Running {' '.join(args)}\n"
    try:
        proc = subprocess.run(
            args,
            text=True,
            check=True,
            capture_output=True,
            timeout=time,
            encoding="utf-8",
        )
        if verbose:
            log += proc.stdout + "\n"
        return log, parse_smt(proc.stdout)
    except subprocess.CalledProcessError as exn:
        if verbose:
            log += exn.output.decode("utf-8") + "\n"
        log += f"Error: {exn}\n"
        return log, {}
    except subprocess.TimeoutExpired as exn:
        partial_output = exn.output.decode("utf-8")
        if verbose:
            log += partial_output + "\n"
        log += f"Timeout (external) after {exn.timeout} seconds: {exn}\n"
        parsed = parse_smt(partial_output)
        parsed["external timeout"] = [exn.timeout]
        return log, parsed


def run_bench(cut, path, z3time, time, verbose):
    log, result = run_nv_smt(path, cut, z3time, time, verbose)
    return (log, cut, result)


def run_benchmarks_sync(benchdir, benches, z3time, time, verbose) -> tuple[str, dict]:
    """
    Run the given benchmarks in the given directory in sequence (once each).
    Return a log of output and a dictionary with the benchmark results for each cut.
    """
    return join_cut_dicts(
        *[
            run_bench(c, os.path.join(benchdir, n), z3time, time, verbose)
            for (c, n) in benches
        ]
    )


def run_benchmarks_parallel(
    benchdir, benches, z3time, time, verbose
) -> tuple[str, dict]:
    """
    Run the given benchmarks in the given directory in parallel (once each).
    Return a log of output and a dictionary with the benchmark results for each cut.
    """
    # set up the args for each run_bench
    paths = map(
        lambda t: (t[0], os.path.join(benchdir, t[1]), z3time, time, verbose), benches
    )

    with multiprocessing.Pool(processes=len(benches)) as pool:
        return join_cut_dicts(
            *pool.starmap(
                run_bench,
                paths,
            )
        )


def run_trials_sync(benchdir, benches, z3time, time, trials, verbose, logfile):
    """
    Run trials of the given benchmarks and return a dictionary of profiling information.
    """
    runs = {}
    for i in range(trials):
        logfile.write("Running trial " + str(i + 1) + " of " + str(trials) + "\n")
        logs, results = run_benchmarks_sync(benchdir, benches, z3time, time, verbose)
        logfile.write(logs)
        runs[i] = results
    return runs


def run_trials_parallel(benchdir, benches, z3time, time, trials, verbose, logfile):
    """
    Run the benchmarks in the given directory and return a dictionary of
    profiling information.
    Runs each trial in parallel.
    """
    with multiprocessing.Pool(processes=trials) as pool:
        args = [(benchdir, benches, z3time, time, verbose) for _ in range(trials)]
        runs = pool.starmap(run_benchmarks_sync, args)
        logs, results = map(list, zip(*runs))
        results = dict(enumerate(results))
        logfile.write("".join(logs))
        return results


def invert_results_dict(results):
    """
    Flatten the results nested dictionary into a CSV-writable format.
    Results has the following nested structure as input:
    dict[directory, dict[trial, dict[cut, dict[operation, list of occurrences]]]]
    The output instead has the form:
    list[dict[str,str]] of N elements, where each element has the following keys:
    - 'trial'
    - 'cut'
    - 'operation'
    - 'occurrence'
    - and a key for each directory
    and N = #trials * #cuts * #operations * #occurrences
    """
    output: dict[tuple, dict] = {}
    for (dir, trials) in results.items():
        for (trial, cuts) in trials.items():
            for (cut, ops) in cuts.items():
                for (op, occurrences) in ops.items():
                    for (i, t) in enumerate(occurrences):
                        common_hash = (trial, cut, op, i)
                        output.setdefault(common_hash, dict())[f"{dir}"] = t
    rows = []
    for ((t, c, o, i), data) in output.items():
        common = {"operation": o, "cut": c, "trial": t, "occurrence": i}
        common.update(data)
        rows.append(common)
    return rows


def write_csv(results: dict[str, dict[str, dict]], path):
    """
    Write the results dictionary to a CSV.
    Each line of the CSV describes an operation run for a given cut during a given trial,
    some number of times (some operations may run many times if the cut produces many subnetworks).
    """
    output = invert_results_dict(results)
    fields = output[0].keys()
    with open(path, "w") as csvf:
        writer = csv.DictWriter(csvf, fieldnames=list(fields), restval="")
        writer.writeheader()
        for row in output:
            writer.writerow(row)


if __name__ == "__main__":
    DIRECTORY = "benchmarks/SinglePrefix/FAT{}"
    SIZES = [4]
    Z3TIMEOUT = 3600
    TIMEOUT = 3600
    TRIALS = 3
    RUNS = {}
    for sz in SIZES:
        benchdir = DIRECTORY.format(sz)
        print(f"Running benchmark {benchdir}")
        benchmarks = [
            (None, f"sp{sz}.nv"),
            ("horizontal", f"sp{sz}-part.nv"),
            # ("vertical", f"sp{sz}-vpart.nv"),
            ("pods", f"sp{sz}-pods.nv"),
        ]
        results = run_trials_parallel(
            benchdir,
            benchmarks,
            Z3TIMEOUT,
            TIMEOUT,
            TRIALS,
            verbose=False,
            logfile=sys.stdout,
        )
        RUNS[benchdir] = results

    write_csv(RUNS, "kirigami-results-test.csv")
