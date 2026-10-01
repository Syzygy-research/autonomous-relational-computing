(* Valis Skeleton for mechanization - static fragment

   Files:
   - Syntax: atomic relations, composition, union, converse, star
   - Denotation: tick-indexed relations
   - Operational: state, small-step relation, scheduler
   - Theorems: soundness, determinism lemma (static fragment)

   This is a minimal starting point. Flesh out definitions before proving
   lemmas.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Module Valis.

  (* Basic identifiers *)
  Definition Id := nat.

  Inductive Expr : Type :=
  | EAtom : Id -> Expr
  | ESeq  : Expr -> Expr -> Expr
  | EUnion : Expr -> Expr -> Expr
  | EConv : Expr -> Expr
  | EStar : Expr -> Expr.

  (* Placeholder types for values and phases *)
  Definition Value := nat.
  Definition Phase := nat.

  (* Tick-indexed denotation: map ticks (nat) to sets of triples *)
  Definition Tick := nat.
  Definition Denotation := Tick -> list (Value * Value * Phase).

  (* State and small-step relation will go here. *)

End Valis.
