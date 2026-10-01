(* A clean dagger category record and an example instantiation from Phase 1 *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Syntax.
Import ListNotations.

Record DaggerCategory := {
  Obj : Type;
  Hom : Obj -> Obj -> Type;

  id : forall {A}, Hom A A;
  comp : forall {A B C}, Hom B C -> Hom A B -> Hom A C;

  dagger : forall {A B}, Hom A B -> Hom B A;

  (* notation helpers *)
  comp_assoc :
    forall {A B C D}
           (f : Hom C D)
           (g : Hom B C)
           (h : Hom A B),
      comp f (comp g h) =
      comp (comp f g) h;

  id_left :
    forall {A B} (f : Hom A B),
      comp id f = f;

  id_right :
    forall {A B} (f : Hom A B),
      comp f id = f;

  dagger_involutive :
    forall {A B} (f : Hom A B),
      dagger (dagger f) = f;

  dagger_contravariant :
    forall {A B C}
           (f : Hom B C)
           (g : Hom A B),
      dagger (comp f g) =
      comp (dagger g) (dagger f);

  dagger_id :
    forall {A},
      dagger (@id A) = id
}.

(* example: single-object category of RelationAtom modulo equivalence *)
(*
Module Phase1Category.

  Definition Obj := unit.

  (* homs are equivalence classes of RelationAtom; we'll use atoms
     themselves but interpret composition/dagger on representatives. *)
  Definition Hom (_ _ : Obj) := RelationAtom.

  Definition id_rel : RelationAtom :=
    {| id := "id";
       source := "x";
       target := "x";
       strength := 0; phase := 0;
       shear := (0,0);
       canonical := true |}.

  Program Definition comp_rel {A B C} (f : Hom B C) (g : Hom A B) : Hom A C :=
    compose_atoms f g.

  Program Definition dagger_rel {A B} (f : Hom A B) : Hom B A :=
    converse f.

  (* we fill the category laws using lemmas from Operational.v *)
  (
    (* comp_assoc *)
    fun A B C D f g h =>
      (* after unfolding definitions, this is exactly compose_assoc *)
      eq_refl
  ) : forall {A B C D} (f:Hom C D) (g:Hom B C) (h:Hom A B),
        comp f (comp g h) = comp (comp f g) h;
  (
    (* id_left *)
    fun A B f => eq_refl
  ) : forall {A B} (f:Hom A B), comp id f = f;
  (
    (* id_right *)
    fun A B f => eq_refl
  ) : forall {A B} (f:Hom A B), comp f id = f;
  (
    (* dagger_involutive *)
    fun A B f => eq_refl
  ) : forall {A B} (f:Hom A B), dagger (dagger f) = f;
  (
    (* dagger_contravariant *)
    fun A B C f g => eq_refl
  ) : forall {A B C} (f:Hom B C) (g:Hom A B),
        dagger (comp f g) = comp (dagger g) (dagger f);
  (
    (* dagger_id *)
    fun A => eq_refl
  ) : forall {A}, dagger (@id A) = id
}.

End Phase1Category.
*)
