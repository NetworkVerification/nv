#!/usr/bin/python3
"""
Compute benchmark results comparing partitioned and unpartitioned SMT checks.
Takes output of runs of NV as input and produces a CSV.
"""
import re
from datetime import datetime
import sys
import csv
from typing import Any


def parse_smt(output: str) -> dict[str, list[int | float]]:
    """
    Parse the output of an NV command.
    Return a dictionary of operations to lists of times taken by those operations.
    """
    action = re.compile(r"(.*) took: (\d*\.?\d+) secs to complete", re.M)
    z3action = re.compile(r"^\s*:(\w*)\s*(\d*\.?\d+)", re.M)
    assertion = re.compile(r"Assertion (\d*) failed", re.M)
    guarantee = re.compile(r"Guarantee (\d*) failed", re.M)
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
        assn = int(match.group(1))
        profile.setdefault("failed asserts", list()).append(assn)
    # get guarantee failures
    for match in guarantee.finditer(output):
        guar = int(match.group(1))
        profile.setdefault("failed guars", list()).append(guar)
    # get z3 timeouts
    for match in z3timeout.finditer(output):
        time = int(match.group(1))
        profile.setdefault("z3 timeout", list()).append(time)
    return profile


def invert_results_dict(
    results: dict[str, dict[str, dict[str, dict[str, list]]]]
) -> list[dict[str, Any]]:
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
    for (benchmark, trials) in results.items():
        for (trial, cuts) in trials.items():
            for (cut, ops) in cuts.items():
                for (op, occurrences) in ops.items():
                    for (i, time) in enumerate(occurrences):
                        common_hash = (trial, cut, op, i)
                        output.setdefault(common_hash, dict())[f"{benchmark}"] = time
    rows = []
    for ((t, c, o, i), data) in output.items():
        common = {"operation": o, "cut": c, "trial": t, "occurrence": i}
        common.update(data)
        rows.append(common)
    return rows


def write_csv(results: dict[str, dict[str, dict]], path: str):
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


def save_results(runs, prefix="kirigami-results"):
    """Save runs to CSV."""
    timestamp = datetime.now()
    time = timestamp.strftime("%Y-%m-%d-%H:%M:%S")
    write_csv(runs, f"{prefix}-{time}.csv")


def tabulate(bench: str, trial: int, cut: str, output: str):
    op_times = parse_smt(output)
    rows = []
    for (operation, times) in op_times.items():
        for (i, t) in enumerate(times):
            rows.append(
                {"operation": operation, "cut": cut, "trial": trial, "occurrence": i}
            )
            # TODO


if __name__ == "__main__":
    for f in sys.argv[1:]:
        with open(f, "r") as data:
            parsed = parse_smt(data.read())
            # TODO: export this parsed data to a results file
