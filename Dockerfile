FROM ubuntu:24.04 AS builder
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y --no-install-recommends \
    g++ \
    gcc \
    git \
    flex \
    bison \
    make \
    curl \
    patch


COPY . /app/ebmc
WORKDIR /app/ebmc

# This Dockerfile assumes the submodule lib/cbmc is already checked out.
RUN make -j$(nproc) -C lib/cbmc/src minisat2-download
RUN make -j$(nproc) -C src

FROM ubuntu:24.04 AS runner
COPY --from=builder /app/ebmc/src/ebmc/ebmc /usr/local/bin/
ENTRYPOINT [ "ebmc" ]
