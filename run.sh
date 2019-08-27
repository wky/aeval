#!/bin/bash





#all pass. full problem solved
time build/tools/bv/bv --chc-file="bench_horn_bv/pipe-1.smt2" --const-bw=2 --ante-size=1 --grammar-file="bench_horn_bv/pipe.gmr" > logs/pipe-1.log
time build/tools/bv/bv --chc-file="bench_horn_bv/pipe-2.smt2" --const-bw=2 --ante-size=1 --grammar-file="bench_horn_bv/pipe.gmr" > logs/pipe-2.log
time build/tools/bv/bv --chc-file="bench_horn_bv/pipe-3.smt2" --const-bw=2 --ante-size=1 --grammar-file="bench_horn_bv/pipe.gmr" > logs/pipe-3.log
time build/tools/bv/bv --chc-file="bench_horn_bv/pipe-4.smt2" --const-bw=2 --ante-size=1 --grammar-file="bench_horn_bv/pipe.gmr" > logs/pipe-4.log



#pass
time build/tools/bv/bv --chc-file="bench_horn_bv/aes-1.smt2" --const-bw=4 --ante-size=1 --conseq-size=1 --conseq-disj=1 --grammar-file="bench_horn_bv/aes.gmr" > logs/aes-1.log
time build/tools/bv/bv --chc-file="bench_horn_bv/aes-2.smt2" --const-bw=4 --ante-size=1 --conseq-size=1 --conseq-disj=1 --grammar-file="bench_horn_bv/aes.gmr" > logs/aes-2.log
time build/tools/bv/bv --chc-file="bench_horn_bv/aes-3.smt2" --const-bw=4 --ante-size=1 --conseq-size=1 --conseq-disj=1 --grammar-file="bench_horn_bv/aes.gmr" > logs/aes-3.log
time build/tools/bv/bv --chc-file="bench_horn_bv/aes-4.smt2" --const-bw=4 --ante-size=1 --conseq-size=1 --conseq-disj=1 --grammar-file="bench_horn_bv/aes.gmr" > logs/aes-4.log

#pass (need unroll 10), don't try yet.
time build/tools/bv/bv --chc-file="bench_horn_bv/aes-5.smt2" --const-bw=4 --ante-size=1 --conseq-size=1 --conseq-disj=1 --grammar-file="bench_horn_bv/aes.gmr" > logs/aes-5.log








