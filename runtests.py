import subprocess

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
    topology_files = ["fattree20", "fattree20-2", "fattree125", "fattree500"]#, "fattree1000"]
    assertions = ["match x[0n] with | None -> false | Some _ -> true", "foldNodes (fun k v acc -> acc && match v with | None -> false | Some _ -> true) x true"]
    for top in topology_files:
        for i, asn in enumerate(assertions):
            filename = "testfiles/" + top + ("_single" if i==0 else "_allpairs") + ".nv"
            f = open(filename, "w")
            f.write("include \"../examples/generic-topologies/" + top + ".nv\"\n")
            f.write("include \"../examples/generic-algebras/distance-allpairs.nv\"\n")
            f.write("let assert n x = " + asn + "\n")
            f.close()
            filenames.append(filename)
    return filenames

def getFilename(f):
    return f.split("/")[-1].split(".")[0]

testfiles = make_testfiles()

for file in testfiles:
    print("Running test on "+file)
    outfile1 = open("output/{}_slicing.txt".format(getFilename(file)), "w")
    # outfile2 = open("output/{}_vanilla.txt".format(getFilename(file)), "w")
    cmd1 = ["./nv", "-m", "-slicing", file]
    # cmd2 = ["./nv", "-m", "-unbox", file]
    subprocess.run(cmd1, stdout=outfile1, stderr=outfile1)
    # subprocess.run(cmd2, stdout=outfile2, stderr=outfile2)
