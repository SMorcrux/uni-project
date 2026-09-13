Two static analyses for the CFG programming language of the project:

parity/parity.py   parity analysis of integer programs        (Section 1)
shape/shape.py     shape analysis of unshared acyclic lists   (Section 2)

Both are single-file Python programs, stdlib only,
nothing to compile or install. Run the programs with:

--------------------
python3 parity/parity.py PROGRAM.txt [--domain=disjunctive|pointwise] [--no-invariants] [--quiet]
python3 shape/shape.py   PROGRAM.txt [--no-invariants] [--quiet] [--max-graphs=N]