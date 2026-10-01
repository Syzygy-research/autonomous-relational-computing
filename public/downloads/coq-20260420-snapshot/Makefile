.PHONY: all core kernel kernel_minimal demo clean

COQ_MAKEFILE ?= coq_makefile
J ?= 2
V ?=

# Default parallelism unless the user already passed -j/--jobs.
ifeq (,$(filter -j% --jobs% -j --jobs,$(MAKEFLAGS)))
MAKEFLAGS += -j$(J)
endif

all: core

# Full verification build (kept separate from the kernel-only build)
core: Makefile.coq
	$(MAKE) -f Makefile.coq V=$(V) all

Makefile.coq: _CoqProject
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

# Kernel-only build gates
kernel: Makefile.kernel
	$(MAKE) -f Makefile.kernel V=$(V) all

Makefile.kernel: _CoqProject.kernel
	$(COQ_MAKEFILE) -f _CoqProject.kernel -o Makefile.kernel

kernel_minimal: Makefile.kernel_minimal
	$(MAKE) -f Makefile.kernel_minimal V=$(V) all

Makefile.kernel_minimal: _CoqProject.kernel_minimal
	$(COQ_MAKEFILE) -f _CoqProject.kernel_minimal -o Makefile.kernel_minimal

# Demo/legacy build (not part of verification gate)
demo: Makefile.demo
	$(MAKE) -f Makefile.demo V=$(V) all

Makefile.demo: _CoqProject.demo
	$(COQ_MAKEFILE) -f _CoqProject.demo -o Makefile.demo

clean:
	rm -f *.vo *.vos *.vok *.glob *.aux *.vio
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d
	rm -f Makefile.kernel Makefile.kernel.conf .Makefile.kernel.d
	rm -f Makefile.kernel_minimal Makefile.kernel_minimal.conf .Makefile.kernel_minimal.d
	rm -f Makefile.demo Makefile.demo.conf .Makefile.demo.d
