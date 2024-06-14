./cvc5 -t cnf -t arith::presolve -t arith -t cadical::propagator --sat-solver=cadical box-or-not.smt2 | less

box-or-not.smt2
```smt2
(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (or (and (> x 40) (< x 45) (> y 20) (< y 25))
            (not (and (> x 10) (or (< x 15) (> y 30)) (< y 35)))))
(assert (or (> z 40) (< x 45) (> y 20)))

(check-sat)
```

CNF file is in myfile.cnf
