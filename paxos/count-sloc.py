import sys

def countfile(dafny_file):
    with open(dafny_file) as f:
        lines = f.readlines()

    lines = [l.strip() for l in lines if len(l.strip()) > 0]
    physical_lines = []

    physical_mode = True
    for l in lines:
        # Strip comment lines
        if physical_mode:
            if "/*" in l:
                if "*/" not in l:   
                    # Begin multi-line comment
                    physical_mode = False
                else:
                    continue
            elif len(l) >= 2 and l[:2] == "//":
                continue
            else:
                physical_lines.append(l)
        else:
            if "*/" in l:
                # End multi-line comment
                physical_mode = True    
    # for l in physical_lines:
    #     print(l)
    print(len(physical_lines))


if __name__ == "__main__":
    # positional arguments <file>
    dafny_file = sys.argv[1]
    if dafny_file[-4:] != ".dfy":
        print("Error: %s not a dafny file" %dafny_file)
        sys.exit(1)
    countfile(dafny_file)