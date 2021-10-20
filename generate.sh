#!/usr/bin/env bash
set -euo pipefail

# generate code for the example signatures
for n in utlc stlc fcbv variadic pi num; do
    echo dune exec -- bin/main.exe signatures/${n}.sig -fext -f -s coq -o case-studies/examples/${n}_wellscoped.v
    dune exec -- bin/main.exe signatures/${n}.sig -fext -f -s coq -o case-studies/examples/${n}_wellscoped.v
done

# just for fol because it uses the cod functor, so it needs functional extensionality 
echo dune exec -- bin/main.exe signatures/fol.sig -fext -f -s coq -o case-studies/examples/fol_wellscoped.v
dune exec -- bin/main.exe signatures/fol.sig -fext -f -s coq -o case-studies/examples/fol_wellscoped.v

for n in utlc stlc fcbv pi num; do
    echo dune exec -- bin/main.exe signatures/${n}.sig -fext -allfv -f -s ucoq -o case-studies/examples/${n}_unscoped.v
    dune exec -- bin/main.exe signatures/${n}.sig -fext -allfv -f -s ucoq -o case-studies/examples/${n}_unscoped.v
done

# generate the code for Kathrin's case study.
KAT="case-studies/kathrin/coq/"
generate_file() {
    file=$1
    scope=$2
    echo dune exec -- bin/main.exe ${KAT}${file}.sig -o ${KAT}${file}.v -s ${scope} -no-static -fext -f
    dune exec -- bin/main.exe ${KAT}${file}.sig -o ${KAT}${file}.v -s ${scope} -no-static -fext -f
}

DATA_DIR='./share/autosubst'
echo cp ${DATA_DIR}/core_809.v ${DATA_DIR}/core_axioms.v ${DATA_DIR}/fintype.v ${DATA_DIR}/fintype_axioms.v ${DATA_DIR}/unscoped.v ${DATA_DIR}/unscoped_axioms.v ${KAT}
cp ${DATA_DIR}/core_axioms.v ${DATA_DIR}/fintype.v ${DATA_DIR}/fintype_axioms.v ${DATA_DIR}/unscoped.v ${DATA_DIR}/unscoped_axioms.v ${KAT}
cp ${DATA_DIR}/core_809.v ${KAT}core.v

# the case study only contains one instance of unscoped code
generate_file "Chapter3/utlc_pure" ucoq

for f in "Chapter3/utlc_scoped" "Chapter6/utlc_pairs" "Chapter6/sysf_cbv" "Chapter6/variadic_fin" "Chapter9/stlc" "Chapter10/sysf" "Chapter10/sysf_pat"; do
    generate_file $f coq
done
