#!/usr/bin/env bash
set -euo pipefail

# removed num fol due to exceptiong while compiling
for n in utlc stlc fcbv variadic pi; do
    echo dune exec -- bin/main.exe signatures/${n}.sig case-studies/${n}/${n}_wellscoped.v coq
    echo dune exec -- bin/main.exe signatures/${n}.sig case-studies/${n}/${n}_unscoped.v ucoq
    dune exec -- bin/main.exe signatures/${n}.sig case-studies/${n}/${n}_wellscoped.v coq
    dune exec -- bin/main.exe signatures/${n}.sig case-studies/${n}/${n}_unscoped.v ucoq
done
