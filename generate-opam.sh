#!/usr/bin/env bash
set -euo pipefail

# We try to support older Rocq versions.
# The simplest solution for the static files I have found is to just use sed
remove_export() {
    sed -i -E -e 's/#\[ export \]//' $1
}

### EXAMPLES
# generate code for the example signatures
for n in utlc stlc fcbv variadic pi num fol logrel_coq; do
    echo autosubst signatures/${n}.sig -fext -f -s rocq -o case-studies/examples/${n}_wellscoped.v
    autosubst signatures/${n}.sig -fext -f -s rocq -o case-studies/examples/${n}_wellscoped.v
done

# allfv is only supported for unscoped syntax so we only turn it on here
for n in utlc stlc fcbv pi num logrel_coq; do
    echo autosubst signatures/${n}.sig -fext -allfv -f -s urocq -o case-studies/examples/${n}_unscoped.v
    autosubst signatures/${n}.sig -fext -allfv -f -s urocq -o case-studies/examples/${n}_unscoped.v
done

### Prelude test
echo autosubst signatures/prelude.sig -o case-studies/examples/prelude_import.v -f -s urocq -fext -p case-studies/prelude/prelude.v
autosubst signatures/prelude.sig -o case-studies/examples/prelude_import.v -f -s urocq -fext -p case-studies/prelude/prelude.v

### TAPL
# generate code for the tapl exercise
echo autosubst case-studies/tapl-exercise/sysf.sig -o case-studies/tapl-exercise/sysf.v -f -s urocq -fext
autosubst case-studies/tapl-exercise/sysf.sig -o case-studies/tapl-exercise/sysf.v -f -s urocq -fext

### KATRIN
# generate the code for Kathrin's case study.
KAT="case-studies/kathrin/rocq/"
DATA_DIR="./share/rocq-autosubst-ocaml"

generate_file() {
    file=$1
    scope=$2
    echo autosubst ${KAT}${file}.sig -o ${KAT}${file}.v -s ${scope} -no-static -f
    autosubst ${KAT}${file}.sig -o ${KAT}${file}.v -s ${scope} -no-static -f
}

echo cp ${DATA_DIR}/core.v ${DATA_DIR}/core_axioms.v ${DATA_DIR}/fintype.v ${DATA_DIR}/fintype_axioms.v ${DATA_DIR}/unscoped.v ${DATA_DIR}/unscoped_axioms.v ${KAT}
cp ${DATA_DIR}/core.v ${DATA_DIR}/core_axioms.v ${DATA_DIR}/fintype.v ${DATA_DIR}/fintype_axioms.v ${DATA_DIR}/unscoped.v ${DATA_DIR}/unscoped_axioms.v ${KAT}

# the case study only contains one instance of unscoped code
generate_file "Chapter3/utlc_pure" urocq

for f in "Chapter3/utlc_scoped" "Chapter6/utlc_pairs" "Chapter6/sysf_cbv" "Chapter6/variadic_fin" "Chapter9/stlc" "Chapter10/sysf" "Chapter10/sysf_pat"; do
    generate_file $f rocq
done
