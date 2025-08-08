FROM ubuntu:24.04 AS base

ARG TARGETARCH
ENV Z3_VERSION=4.13.4
ENV ELDARICA_VERSION=2.1

RUN apt update && apt install -y curl wget unzip build-essential git
# opam
WORKDIR /tmp
RUN curl -fsSL https://opam.ocaml.org/install.sh > opam.sh && \
    yes "" | bash opam.sh && \
    opam init --disable-sandboxing

# rustup (for hoice)
WORKDIR /tmp
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh && \
    chmod +x rustup.sh && \
    ./rustup.sh -y
ENV PATH="/root/.cargo/bin:${PATH}"

# Z3 for (hoice)
RUN echo ${TARGETARCH} && \
    case ${TARGETARCH} in \
        amd64) \
            BASE="z3-${Z3_VERSION}-x64-glibc-2.35"; \
            URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${BASE}.zip";; \
        arm64) \
            # The glibc version is different from that of x64
            BASE="z3-${Z3_VERSION}-arm64-glibc-2.34"; \
            URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${BASE}.zip";; \
        *) \
            echo "Unsupported architecture: ${TARGETARCH}"; \
            exit 1;; \
     esac && \
    wget ${URL} && \
    unzip ${BASE}.zip && \
    cp ${BASE}/bin/z3 /usr/local/bin

# Hoice
WORKDIR /tmp
RUN . $HOME/.cargo/env && \
    cargo install --git https://github.com/hopv/hoice

# Eldarica
WORKDIR /tmp
RUN wget https://github.com/uuverifiers/eldarica/releases/download/v${ELDARICA_VERSION}/eldarica-bin-${ELDARICA_VERSION}.zip && \
    unzip eldarica-bin-2.1.zip && \
    mv eldarica /usr/local/bin && \
    ln -s /usr/local/bin/eldarica/eld /usr/local/bin/eld && \
    apt install -y default-jre

FROM base AS builder
COPY ./ /root/rethfl
WORKDIR /root/rethfl
RUN opam switch create . --deps-only --locked --yes && \
    eval $(opam env) && \
    dune build @install && \
    dune install

ENV OPAMSWITCH="/root/rethfl"
ENTRYPOINT ["opam", "exec", "--"]
CMD ["rethfl"]
