import glob

# Recursively list all files in the directory
def get_all_files(path):
    return [f for f in glob.glob(path + "**/*.nv", recursive=True)]

def update_file(file):
    f = open(file, "r+")
    has_assert = False
    has_init = False
    has_trans = False
    has_merge = False
    def process_line(line):
        nonlocal has_assert
        nonlocal has_init
        nonlocal has_trans
        nonlocal has_merge
        if line.strip().startswith("let assert"):
            has_assert = True
            line = "let assert_node" + line.strip()[10:] + "\n"
        if line.strip().startswith("let init "):
            has_init = True
            line = "let init_" + line.strip()[8:] + "\n"
        if line.strip().startswith("let trans "):
            has_trans = True
            line = "let trans_" + line.strip()[9:] + "\n"
        if line.strip().startswith("let merge "):
            has_merge = True
            line = "let merge_" + line.strip()[9:] + "\n"
        return line
    lines = [process_line(line) for line in f.readlines()]
    if has_init: lines.append("let init = init_\n")
    if has_trans: lines.append("let trans = trans_\n")
    if has_merge: lines.append("let merge = merge_\n")
    if has_init and has_trans and has_merge:
        lines.append("let sol = solution {init = init_; trans = trans_; merge = merge_}\n\n")
    if has_assert:
        lines.append("assert foldNodes (fun k v acc -> acc && assert_node k v) sol true\n")
    f = open(file, "w")
    f.writelines(lines)

for file in get_all_files(""):
    print(file)
    update_file(file)
