FROM mcr.microsoft.com/devcontainers/base:2.1.15-debian13

RUN apt-get update && apt-get install -y \
    tig

USER vscode

# install Lean
ARG LEAN_VERSION=leanprover/lean4:v4.3.0
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain ${LEAN_VERSION}
ENV PATH="/home/vscode/.elan/bin:${PATH}"
RUN elan toolchain install ${LEAN_VERSION}
