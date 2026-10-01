## Admitted Theorems Requiring Proof Development

The Valis v1 release includes a Coq mechanization with the following admitted theorems that need robust proofs:

### compose_rel_membership
- Location: `tools/coq/Valis_Composition.v`
- Status: Admitted due to unification issues in `in_map_iff`/`filter` tactics
- Specification: `forall R S T x z, In (x,z) (compose_rel (compose_rel R S) T) <-> In (x,z) (compose_rel R (compose_rel S T))`

### compose_assoc_inclusion_left
- Location: `tools/coq/Valis_Composition.v`
- Status: Admitted due to brittle equality handling
- Specification: Inclusion lemma used in associativity proof

### converse_deterministic
- Location: `tools/coq/Valis_Composition.v`
- Status: Admitted due to `map_id` unification failure
- Specification: `forall r, converse_rel (converse_rel r) = r`

### lists_perm_of_same_members
- Location: `tools/coq/Valis_Composition.v`
- Status: Admitted due to contradiction tactic issues
- Specification: `forall l1 l2, NoDup l1 -> NoDup l2 -> (forall x, In x l1 <-> In x l2) -> Permutation l1 l2`

## Notes
- All definitions and type signatures are stable and safe for downstream use.
- The theorems are fully specified and believed correct; the current `Admitted` placeholders are due to tactic engineering challenges rather than theoretical issues.
- The Coq file compiles and typechecks with the admits; we prefer replacing admits with robust proofs in follow-up work.

## Acceptance Criteria
- Replace all `Admitted` with fully checked proofs (`Qed`).
- Proofs should avoid brittle tactic-order dependencies (prefer `remember`, explicit destruct, or small lemmas).
- Maintain compatibility with existing definitions and downstream users.

## Priority
High — required for complete formal verification of Valis relational composition.

Assign to: @me
Labels: coq, priority:high
