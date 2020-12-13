#!/usr/bin/env bash
set -euo pipefail

for n in utlc stlc fcbv variadic pi num fol; do
    echo dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}/${n}_wellscoped.v coq
    dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}/${n}_wellscoped.v coq
done

for n in utlc stlc fcbv pi num; do
    echo dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}/${n}_unscoped.v ucoq
    dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}/${n}_unscoped.v ucoq
done
