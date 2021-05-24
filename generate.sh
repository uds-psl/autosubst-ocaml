#!/usr/bin/env bash
set -euo pipefail

# # generate code for the example signatures
# for n in utlc stlc fcbv variadic pi num fol; do
#     echo dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}_wellscoped.v coq
#     dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}_wellscoped.v coq
# done

# for n in utlc stlc fcbv pi num; do
#     echo dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}_unscoped.v ucoq
#     dune exec -- bin/main.exe signatures/${n}.sig case-studies/examples/${n}_unscoped.v ucoq
# done

# generate the code for Kathrin's case study.
# Since I don't generate tactics and typeclasses I used the ones from Kathrin and append them to the code I generated
KAT="case-studies/kathrin/coq/"
generate_file() {
    file=$1
    scope=$2
    echo dune exec -- bin/main.exe ${KAT}${file}.sig ${KAT}${file}.v ${scope}
    dune exec -- bin/main.exe ${KAT}${file}.sig ${KAT}${file}.v ${scope}
}
append_tactics() {
    file=$1
    echo cat ${KAT}${file}_axioms.v ${KAT}${file}_rest.v > ${KAT}${file}_axioms.v
    cat ${KAT}${file}_axioms.v ${KAT}${file}_rest.v > ${KAT}${file}_axioms.v
}

# echo cp data/core.v data/core_axioms.v data/fintype_809.v data/unscoped_809.v ${KAT}
# cp data/core.v data/core_axioms.v data/fintype_809.v data/unscoped_809.v ${KAT}

# the case study only contains one instance of unscoped code
generate_file "Chapter3/utlc_pure" ucoq
# append_tactics "Chapter3/utlc_pure"

for f in "Chapter3/utlc_scoped" "Chapter6/utlc_pairs" "Chapter6/sysf_cbv" "Chapter6/variadic_fin" "Chapter9/stlc" "Chapter10/sysf" "Chapter10/sysf_pat"; do
    generate_file $f coq
    # append_tactics $f
done
