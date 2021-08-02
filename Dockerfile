FROM ocaml/opam:alpine-ocaml-4.11-flambda as builder

# based on https://medium.com/@bobbypriambodo/lightweight-ocaml-docker-images-with-multi-stage-builds-f7a060c7fce4

COPY bin bin
COPY lib lib
COPY monadiclib monadiclib

ENV OPAMYES true

RUN sudo apk add gmp-dev && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam install dune coq.8.13.2 angstrom ocamlgraph ppx_deriving && \
    eval $(opam env) && \
    dune build


FROM ocaml/opam:alpine-ocaml-4.11-flambda

COPY --from=builder /home/opam/_build/default/bin/main.exe ./main.exe
COPY data data

COPY ./entrypoint.sh ./entrypoint.sh
RUN sudo chown opam:opam ./entrypoint.sh

ENTRYPOINT ./entrypoint.sh
