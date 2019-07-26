import sys
import os
import subprocess

# Run with "python3 dependencies.py [srcdir] [--only-dune-libraries]"

# Call ocamldep
def getAllDeps(srcdir) :
    find_cmd = ["find", ".", "-name", "*.ml"]
    mlfiles = subprocess.run(find_cmd, capture_output=True, universal_newlines=True).stdout
    mlfiles = mlfiles.split("\n")[:-1] # Last elt is empty string, so drop it
    cmd = ["ocamldep", "-all", "-modules"]
    output = subprocess.run(cmd + mlfiles, capture_output=True, universal_newlines=True).stdout
    lines = output.split("\n")[:-1]
    file_and_deps = [line.split(" ") for line in lines]
    return file_and_deps

# Put all dependencies into a dictionary that mirrors the filesystem
def parse_ocamldep_output(lines, allDeps, onlyDuneLibs):
    for line in lines:
        file = line[0][:-1]
        filepath = file.split("/")[1:]
        filename = filepath[-1]
        filepath = filepath[:-1]

        deps = allDeps
        for dir in filepath: # Walk through dict until we get to the last directory
            deps[dir] = deps.get(dir, {})
            deps = deps[dir]
        fdeps = line[1:]
        if onlyDuneLibs:
            fdeps = [d for d in fdeps if d.startswith("Nv_")]
        deps[filename] = fdeps # Add dependencies for this file

# Compute dependencies for each directory
def compute_dirdeps(deps):
    dirdeps = []
    for file_or_subdir in deps.keys():
        if file_or_subdir.endswith(".ml"):
            dirdeps += deps[file_or_subdir]
        else:
            compute_dirdeps(deps[file_or_subdir])
            dirdeps += deps[file_or_subdir]["DirDeps"]
    deps["DirDeps"] = list(dict.fromkeys(dirdeps))

# Print contents of the dictionary
def print_deps(deps, name, pad):
    if pad == "":
        print(name) # Top level has all dependencies, so don't bother printing
    else:
        print(pad + name + ": " + " ".join(deps["DirDeps"]))
    pad = pad + "  "
    for file_or_subdir in deps.keys():
        if file_or_subdir == "DirDeps":
            continue
        elif file_or_subdir.endswith(".ml"):
            print(pad + file_or_subdir + ": " + " ".join(deps[file_or_subdir]))
        else:
            print_deps(deps[file_or_subdir], file_or_subdir, pad)

def parse_args():
    args = {"srcdir" : ".", "only-dune-libraries": False}
    for arg in sys.argv[1:]:
        if not arg.startswith("-"):
            args["srcdir"] = arg
        elif arg == "--only-dune-libraries":
            args["only-dune-libraries"] = True
    return args



def main():
    args = parse_args()

    srcdir = args["srcdir"]
    os.chdir(srcdir)
    allDeps = {}

    ocamldep_output = getAllDeps(srcdir)
    parse_ocamldep_output(ocamldep_output, allDeps, args["only-dune-libraries"])
    compute_dirdeps(allDeps)
    print_deps(allDeps, srcdir, "")

if __name__ == "__main__":
    main()
