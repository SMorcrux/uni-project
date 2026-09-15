Two static analyses for the CFG programming language of the project:

parity/parity.py   parity analysis of integer programs        (Section 1)
shape/shape.py     shape analysis of unshared acyclic lists   (Section 2)

Both are single-file Python programs, stdlib only,
nothing to compile or install. Run the programs with:

--------------------
python3 parity.py PROGRAM.txt
python3 shape.py   PROGRAM.txt