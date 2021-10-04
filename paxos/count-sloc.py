import sys

def countfile(dafny_file):
    with open(dafny_file) as f:
        lines = f.readlines()

    lines = [l.strip() for l in lines if len(l.strip()) > 0]
    logical_lines = []

    logical_mode = True
    for l in lines:
        # Strip comment lines
        if logical_mode:
            if "/*" in l:
                if "*/" not in l:   
                    # Begin multi-line comment
                    logical_mode = False
                else:
                    continue
            elif len(l) >= 2 and l[:2] == "//":
                continue
            else:
                logical_lines.append(l)
        else:
            if "*/" in l:
                # End multi-line comment
                logical_mode = True    
    # for l in logical_lines:
    #     print(l)
    print(len(logical_lines))


if __name__ == "__main__":
    # positional arguments <file>
    dafny_file = sys.argv[1]
    if dafny_file[-4:] != ".dfy":
        print("Error: %s not a dafny file" %dafny_file)
        sys.exit(1)
    countfile(dafny_file)