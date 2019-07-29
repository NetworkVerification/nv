import sys
import os
import subprocess

''' Run with
"python3 dependencies.py [srcdir] [--only-dune-libraries] [--no-dune-libraries]
[--no-externals] [--no-internal-modules]"

The arguments are as follows:
 * srcdir : The directory containing the files to run dependency analysis on
 * --only-dune-libraries : Only show dependencies corresponding to dune libraries,
                           i.e. the folders which contain a dune file
 * --no-dune-libraries : Opposite of the above
 * --no-externals : Don't show dependencies on external modules like Batteries
 * --no-internal-modules : Resolve dependencies for modules which are declared
                           inside a source file to that file. For example,
                           a file which depends on ExpSet will be listed as
                           depending on Collections instead.
'''

def is_external(s):
    return s in \
    ["Batteries", "BatList", "BatMap", "BatSet", "BatEnum", "ANSITerminal", \
     "Hashtbl", "Lazy", "Printf", "Sys", "Array", "Pervasives", "Printexc", \
     "Z", "Big_int_Z", "Weak", "Lru_cache", "Set", "Int64", "Unix", "BatUnix", \
     "Thread", "BatPervasives", "BatString", "Unsigned", "PMap", "PSet", "List", \
     "Buffer", "Graph", "Queue", "Str", "String", "Map", "Cudd", "BatOption",
     "BatUref"]

def is_dune_library(s):
    return s.startswith("Nv_")

# Map modules which are declared inside a file to that file; return all other
# module names unchanges
def map_to_src_file(s):
    modulemap = {"EdgeMap" : "AdjGraph", \
                 "ExpMap" : "Collections", \
                 "ExpSet" : "Collections", \
                 "ValueSet" : "Collections", \
                 "ValueMap" : "Collections", \
                 "TypeMap" : "Collections", \
                 "ConstantSet" : "SmtUtils", \
                 "IntMap" : "PrimitiveCollections", \
                 "IntSet" : "PrimitiveCollections", \
                 "StringMap" : "PrimitiveCollections", \
                 "StringSet" : "PrimitiveCollections", \
                 "StringSetSet" : "PrimitiveCollections"}
    return modulemap.get(s, s)

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
def parse_ocamldep_output(args, lines, allDeps):
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
        if args.get("no-externals", False):
            fdeps = [d for d in fdeps if not is_external(d)]
        if args.get("only-dune-libraries", False):
            fdeps = [d for d in fdeps if is_dune_library(d)]
        if args.get("no-dune-libraries", False):
            fdeps = [d for d in fdeps if not is_dune_library(d)]
        if args.get("no-internal-modules", False):
            fdeps = list(set([map_to_src_file(d) for d in fdeps]))
        fdeps.sort()
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
        elif arg == "--no-externals":
            args["no-externals"] = True
        elif arg == "--no-internal-modules":
            args["no-internal-modules"] = True
        elif arg == "--no-dune-libraries":
            args["no-dune-libraries"] = True
    return args

def main():
    args = parse_args()

    srcdir = args["srcdir"]
    os.chdir(srcdir)
    allDeps = {}

    ocamldep_output = getAllDeps(srcdir)
    parse_ocamldep_output(args, ocamldep_output, allDeps)
    compute_dirdeps(allDeps)
    print_deps(allDeps, srcdir, "")

if __name__ == "__main__":
    main()
