FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive
ENV SPIN_VERSION=6.5.2

RUN apt-get update && apt-get install -y \
    build-essential \
    gcc \
    make \
    bison \
    flex \
    spin \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /spin_artifact


COPY gpu_no_pipeline.pml /spin_artifact/
COPY gpu_triangles.pml /spin_artifact/
COPY gpu_trigo.pml /spin_artifact
COPY gpu_verticles.pml /spin_artifact/

COPY run_helicopter_demo.sh /spin_artifact/
RUN chmod +x /spin_artifact/run_helicopter_demo.sh

WORKDIR /spin_artifact

CMD ["bash", "-c", "./run_helicopter_demo.sh"]
