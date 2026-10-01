FROM coqorg/coq:8.18

# Prepare a container image able to build the kernel_minimal target.
WORKDIR /src

# Ensure basic build tools and git-lfs are available
RUN apt-get update \
 && apt-get install -y --no-install-recommends git-lfs make ca-certificates \
 && rm -rf /var/lib/apt/lists/* \
 && git lfs install --system || true

# Copy repository contents at build/run time (the build script mounts the
# working tree so this Dockerfile is primarily used to pin the Coq runtime).
COPY . /src

CMD ["/bin/bash"]
