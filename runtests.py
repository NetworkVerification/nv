import subprocess, os

testfiles = [
# "fattree.nv",
"batfish.nv",
"batfish3.nv",
# "batfish2.nv",

"FAT2/fat2.nv",
"FAT4/fat4.nv",
"FAT8/fat8.nv",
"FAT12/fat12.nv",

# "fattree-policy-1000.nv"

"FBFAT12-6/fbfattree12-6.nv",
"FBFAT12/fbfattree12.nv",
"FBFAT16/fbfattree16l.nv",
"FBFAT16/fbfattree16.nv",
"FBFAT20/fbfattree20.nv",

"FAT16/fat16.nv",
"FAT20/fat20-policy.nv",
"FAT20/fat20-drop-agg.nv",
]
testfiles = ["examples/" + f for f in testfiles]

def make_testfiles():
    filenames = []
    topology_files = ["fattree20", "fattree20-2", "fattree125", "fattree500", "fattree1000"]
    assertions = [\
        "match x with | None -> false | Some x -> match x[0n] with | None -> false | Some _ -> true", \
        "match x with | None -> false | Some x -> foldNodes (fun k v acc -> acc && match v with | None -> false | Some _ -> true) x true"]
    for top in topology_files:
        for i, asn in enumerate(assertions):
            filename = "testfiles/" + top + ("_single" if i==0 else "_allpairs") + ".nv"
            f = open(filename, "w")
            f.write("include \"../examples/generic-topologies/" + top + ".nv\"\n")
            f.write("include \"../examples/generic-algebras/distance-allpairs-failures.nv\"\n")
            f.write("let assert n x = " + asn + "\n")
            f.close()
            filenames.append(filename)
    return filenames

def getFilename(f):
    return f.split("/")[-1].split(".")[0]

testfiles = make_testfiles()

for file in testfiles:
    print("Running test on "+file)
    ocaml_env = os.environ.copy()
    ocaml_env["OCAMLRUNPARAM"] = "s=8M,i=64M,o=150"
    outfile = open("output/{}_parallel4.txt".format(getFilename(file)), "w")
    cmd = ["time", "./nv", "-m", "-slicing", "-p", "4", file]
    subprocess.run(cmd, stdout=outfile, stderr=outfile, env=ocaml_env)

    outfile = open("output/{}_slicing.txt".format(getFilename(file)), "w")
    cmd = ["time", "./nv", "-m", "-slicing", file]
    subprocess.run(cmd, stdout=outfile, stderr=outfile, env=ocaml_env)

    if not ("500" in file or "1000" in file): # Don't even try without slicing
        outfile = open("output/{}_vanilla.txt".format(getFilename(file)), "w")
        cmd2 = ["time", "./nv", "-m", "-unbox", file]
        subprocess.run(cmd2, stdout=outfile, stderr=outfile, env=ocaml_env)
