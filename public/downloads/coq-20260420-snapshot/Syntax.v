(* VALIS Syntax - Coq skeleton *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

(* Basic identifiers and relation atoms *)
Definition RelId := string.
Definition Entity := string.

(* Relation parameters: strength, phase, shear *)
Record RelationAtom := {
  id : RelId;
  source : Entity;
  target : Entity;
  strength : R;   (* real number between 0 and 1 *)
  phase : R;      (* radians in [0,2*pi) *)
  shear : (R * R);
  canonical : bool;
}.

(* Normalize an atom to canonical orientation. Deterministic and
   idempotent: if the atom is already canonical it is returned unchanged;
   otherwise we return the conversed atom with `canonical := true`.
   This function is kept purely syntactic here; semantic preservation
   lemmas are established in `Denotation.v` when the atom->tuple mapping
   is fleshed out. *)
Definition normalize_atom (a : RelationAtom) : RelationAtom :=
  if canonical a then a else
    {| id := id a;
       source := target a;
       target := source a;
       strength := strength a;
       phase := phase a;
       shear := shear a;
       canonical := true |}.

Lemma normalize_atom_idempotent : forall a,
  normalize_atom (normalize_atom a) = normalize_atom a.
Proof.
  intros a.
  unfold normalize_atom.
  destruct (canonical a) eqn:Heq; simpl.
  - (* a already canonical *)
    rewrite Heq. simpl. reflexivity.
  - (* a non-canonical; after normalization we produce a canonical atom *)
    simpl. (* canonical field of the normalized atom is true, so the second
                application is a no-op and both sides reduce to the same term. *)
    reflexivity.
Qed.

(* Expression syntax *)
Inductive Expr : Type :=
| EAtom : RelId -> Expr
| ESeq : Expr -> Expr -> Expr
| EUnion : Expr -> Expr -> Expr
| EConv : Expr -> Expr
| EStar : Expr -> Expr
| EEmbed : Expr -> R -> R -> Expr   (* sigma, rho *)
| EModulate : Expr -> R -> R -> Expr (* phi, sigma *).
