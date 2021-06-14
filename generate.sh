#!/usr/bin/env bash
set -euo pipefail

# generate code for the example signatures
for n in utlc stlc fcbv variadic pi num; do
    echo dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}_wellscoped.v coq ge810 true true true
    dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}_wellscoped.v coq ge810 true true true
done

# just for fol because it uses the cod functor, so it needs functional extensionality 
echo dune exec -- bin/main.exe signatures/fol.sig case-studies/examples/fol_wellscoped.v coq ge810 false true true
dune exec -- bin/main.exe signatures/fol.sig case-studies/examples/fol_wellscoped.v coq ge810 false true true

for n in utlc stlc fcbv pi num; do
    echo dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}_unscoped.v ucoq ge810 true true true
    dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}_unscoped.v ucoq ge810 true true true
done

# generate the code for Kathrin's case study.
KAT="case-studies/kathrin/coq/"
generate_file() {
    file=$1
    scope=$2
    echo dune exec -- bin/main.exe ${KAT}${file}.sig ${KAT}${file}.v ${scope} ge810 false false true
    dune exec -- bin/main.exe ${KAT}${file}.sig ${KAT}${file}.v ${scope} ge810 false false true
}

echo cp data/core_809.v data/core_axioms.v data/fintype.v data/fintype_axioms.v data/unscoped.v data/unscoped_axioms.v ${KAT}
cp data/core_axioms.v data/fintype.v data/fintype_axioms.v data/unscoped.v data/unscoped_axioms.v ${KAT}
cp data/core_809.v ${KAT}core.v

# the case study only contains one instance of unscoped code
generate_file "Chapter3/utlc_pure" ucoq

for f in "Chapter3/utlc_scoped" "Chapter6/utlc_pairs" "Chapter6/sysf_cbv" "Chapter6/variadic_fin" "Chapter9/stlc" "Chapter10/sysf" "Chapter10/sysf_pat"; do
    generate_file $f coq
done
