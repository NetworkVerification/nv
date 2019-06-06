import subprocess

testfiles = [
 "fattree.nv",
"batfish.nv",
"batfish3.nv",
# "batfish2.nv",

"FAT2/fat2.nv",
"FAT4/fat4.nv",
"FAT8/fat8.nv",
"FAT12/fat12.nv",

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

def getFilename(f):
    return f.split("/")[-1].split(".")[0]

for file in testfiles:
    print("Running test on "+file)
    outfile1 = open("output/{}_hiding.txt".format(getFilename(file)), "w")
    outfile2 = open("output/{}.txt".format(getFilename(file)), "w")
    cmd1 = ["./Main.native", "-m", "-hiding", file]
    cmd2 = ["./Main.native", "-m", "-unbox", file]
    subprocess.run(cmd1, stdout=outfile1, stderr=outfile1)
    subprocess.run(cmd2, stdout=outfile2, stderr=outfile2)
