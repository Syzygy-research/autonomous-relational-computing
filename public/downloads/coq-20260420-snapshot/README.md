# Coq proof snapshot

This directory contains a bounded Coq proof/source snapshot from the VALIS formal kernel review bundle.

Evidence class: FORMALLY ESTABLISHED WITHIN DECLARED MODEL for the sealed kernel scope only.

Sealed kernel scope: `_CoqProject.kernel`. Repository scan found no `Admitted.` or `admit.` placeholders in that scope.

The broader snapshot also includes exploratory Phase 2, geometry, and economics material. Some of those exploratory files contain `Admitted.` or `admit.` placeholders and must not be represented as closed proof.

Boundary: these files support the historical/formal kernel lineage. They do not by themselves establish production KORE conformance, current CR-Core implementation correspondence, external certification, universal AI safety, or underwriting validity.

Primary reproduction target: `make -C public/downloads/coq-20260420-snapshot kernel`.

See `../coq-proof-snapshot-manifest.json` for file digests and placeholder scan results.
