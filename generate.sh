#!/usr/bin/env bash
set -euo pipefail

# We try to support older Coq versions.
# The simplest solution for the static files I have found is to just use sed
remove_export() {
    sed -i -E -e 's/#\[ export \]//' $1
}

### EXAMPLES
# generate code for the example signatures
for n in utlc stlc fcbv variadic pi num fol logrel_coq; do
    echo dune exec -- bin/main.exe signatures/${n}.sig -fext -f -s coq -o case-studies/examples/${n}_wellscoped.v
    dune exec -- bin/main.exe signatures/${n}.sig -fext -f -s coq -o case-studies/examples/${n}_wellscoped.v
done

# allfv is only supported for unscoped syntax so we only turn it on here
for n in utlc stlc fcbv pi num; do
    echo dune exec -- bin/main.exe signatures/${n}.sig -fext -allfv -f -s ucoq -o case-studies/examples/${n}_unscoped.v
    dune exec -- bin/main.exe signatures/${n}.sig -fext -allfv -f -s ucoq -o case-studies/examples/${n}_unscoped.v
done

# We generate the same examples again but for an older Coq version.
# At the moment, this only removes '#[ export ]' attributes of hints.
### EXAMPLES < Coq 8.12
for n in utlc stlc fcbv variadic pi num fol; do
    echo dune exec -- bin/main.exe signatures/${n}.sig -fext -f -s coq -o case-studies/examples-lt813/${n}_wellscoped.v -v lt813
    dune exec -- bin/main.exe signatures/${n}.sig -fext -f -s coq -o case-studies/examples-lt813/${n}_wellscoped.v -v lt813
done

for n in utlc stlc fcbv pi num; do
    echo dune exec -- bin/main.exe signatures/${n}.sig -fext -allfv -f -s ucoq -o case-studies/examples-lt813/${n}_unscoped.v -v lt813
    dune exec -- bin/main.exe signatures/${n}.sig -fext -allfv -f -s ucoq -o case-studies/examples-lt813/${n}_unscoped.v -v lt813
done

echo "altering static files for examples in Coq < 8.12"
remove_export "case-studies/examples-lt813/unscoped.v"
remove_export "case-studies/examples-lt813/fintype.v"


### TAPL
# generate code for the tapl exercise
echo dune exec -- bin/main.exe case-studies/tapl-exercise/sysf.sig -o case-studies/tapl-exercise/sysf.v -f -s ucoq -fext
dune exec -- bin/main.exe case-studies/tapl-exercise/sysf.sig -o case-studies/tapl-exercise/sysf.v -f -s ucoq -fext

### KATRIN
# generate the code for Kathrin's case study.
KAT="case-studies/kathrin/coq/"
DATA_DIR="./share/coq-autosubst-ocaml"

generate_file() {
    file=$1
    scope=$2
    echo dune exec -- bin/main.exe ${KAT}${file}.sig -o ${KAT}${file}.v -s ${scope} -no-static -f -v lt813
    dune exec -- bin/main.exe ${KAT}${file}.sig -o ${KAT}${file}.v -s ${scope} -no-static -f -v lt813
}

echo cp ${DATA_DIR}/core.v ${DATA_DIR}/core_axioms.v ${DATA_DIR}/fintype.v ${DATA_DIR}/fintype_axioms.v ${DATA_DIR}/unscoped.v ${DATA_DIR}/unscoped_axioms.v ${KAT}
cp ${DATA_DIR}/core.v ${DATA_DIR}/core_axioms.v ${DATA_DIR}/fintype.v ${DATA_DIR}/fintype_axioms.v ${DATA_DIR}/unscoped.v ${DATA_DIR}/unscoped_axioms.v ${KAT}

echo "altering static files for Coq 8.9"
sed -i -E -e 's/Declare Scope fscope./(* not supported in Coq 8.9 *)/' -e 's/Declare Scope subst_scope./(* not supported in Coq 8.9 *)/' ${KAT}core.v
remove_export "${KAT}unscoped.v"
remove_export "${KAT}fintype.v"


# the case study only contains one instance of unscoped code
generate_file "Chapter3/utlc_pure" ucoq

for f in "Chapter3/utlc_scoped" "Chapter6/utlc_pairs" "Chapter6/sysf_cbv" "Chapter6/variadic_fin" "Chapter9/stlc" "Chapter10/sysf" "Chapter10/sysf_pat"; do
    generate_file $f coq
done
