From Coq Require Import List Arith.
Import ListNotations.

(* NOTE:
    - The sealed Phase-1 kernel + primitive-aligned economics parameters live in:
          economics/RelationalEconomics_Params_KernelInstanceCurrent_Nat.v
    - This file is an OCaml extraction demo, so it intentionally uses a
       nat-only kernel (no Coq Reals) to keep extracted code runnable without
       realizing classical-real axioms. *)

(* Concrete nat-only kernel instance. *)
Require Import VALIS.Kernel_Implementation.

Module K := ConcreteKernel.

Module RelationalEconomics_ExtractionDemo.
   Definition Amount := nat.
   Definition zero : Amount := 0.
   Definition add : Amount -> Amount -> Amount := Nat.add.
   Definition leq : Amount -> Amount -> Prop := Nat.le.

   Local Infix "+" := add.
   Local Infix "<=" := leq.

   Record Identity := {
      id_hash : K.hash;
      bonded_stake : Amount;
   }.

   Record Contribution := {
      contributor : Identity;
      relation_hash : K.hash;
      contribution_weight : Amount;
   }.

   Definition Ledger := list Contribution.

   Fixpoint identity_minted (i : Identity) (L : Ledger) : Amount :=
      match L with
      | [] => zero
      | c :: rest =>
            let rest_sum := identity_minted i rest in
            if Nat.eq_dec (id_hash (contributor c)) (id_hash i)
            then contribution_weight c + rest_sum
            else rest_sum
      end.

   Fixpoint total_supply (L : Ledger) : Amount :=
      match L with
      | [] => zero
      | c :: rest => contribution_weight c + total_supply rest
      end.

   Fixpoint total_stake (ids : list Identity) : Amount :=
      match ids with
      | [] => zero
      | i :: rest => bonded_stake i + total_stake rest
      end.

   (* Deterministic spam ledger generator (no randomness): creates n unit-weight
       contributions for a single identity. *)
   Fixpoint spam_ledger (i : Identity) (n : nat) : Ledger :=
      match n with
      | 0 => []
      | S n' =>
            {| contributor := i;
                relation_hash := 0; (* dummy hash value for simulation *)
                contribution_weight := 1 |}
            :: spam_ledger i n'
      end.
End RelationalEconomics_ExtractionDemo.

(* Extract these to OCaml so you can run spam-plateau calculations. *)
Require Extraction.
Extraction Language OCaml.
Extraction "relational_economics_demo.ml"
   RelationalEconomics_ExtractionDemo.identity_minted
   RelationalEconomics_ExtractionDemo.total_supply
   RelationalEconomics_ExtractionDemo.total_stake
   RelationalEconomics_ExtractionDemo.spam_ledger.
