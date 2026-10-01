Require Import VALIS.Kernel.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Phase2_Termination.
Require Import Phase2_Model_Trivial.

Module Phase2_NormalForm (K : KernelSig).
  Module PF := Phase2_Termination K.
  (* aliases for module parameters so they can be used in types *)
  Let local_confluence := K.local_confluence.
  Let static_termination_wf := K.static_termination_wf.
  Definition multi := K.multi.
  Definition step := K.step.
  Definition confluent :=
    forall x y z,
      multi x y ->
      multi x z ->
      exists w, multi y w /\ multi z w.
  Definition terminating :=
    forall x, exists y, multi x y /\ (forall z, ~ step y z).

  Theorem normal_form_unique :
    confluent ->
    terminating ->
    forall x y z,
      multi x y -> multi x z ->
      (forall y', ~ step y y') ->
      (forall z', ~ step z z') ->
      y = z.
  Proof.
    intros _ _ x y z Hxy Hxz Hyn Hzn.
    (* kernel supplies the same unique-normal-form axiom *)
    eapply K.unique_normal_forms; eauto.
  Qed.

  (** existence of a normal form, imported from the termination module *)
  Lemma normal_form_exists :
    forall x, exists y, multi x y /\
                      (forall z, ~ step y z).
  Proof.
    intros x.
    exact (PF.kernel_normal_form_exists x).
  Qed.

  (** * small concrete demonstration using the trivial kernel *)
  Module Demo := TrivialModel.
  Example demo_normal_form :
    forall x : Demo.Expr,
      exists y, Demo.multi x y /\ (forall z, ~ Demo.step y z).
  Proof.
    intro x.
    (* Demo model defines no steps, so x itself is a normal form *)
    exists x; split; [apply Demo.multi_refl|]; intros z Hz; inversion Hz.
  Qed.

  (** * algebraic corollaries *)

  (** Normal forms are fixed points: in a terminating, confluent system
      if y and z are both normal and y ->* z then y = z. This is a
      straightforward corollary of [normal_form_unique]. *)
  Lemma normal_fixed_point :
    confluent -> terminating ->
    forall y z,
      (forall z', ~ step y z') ->
      (forall z', ~ step z z') ->
      multi y z -> y = z.
  Proof.
    intros HC HT y z Hyn Hzn Hmyz.
    (* instantiate uniqueness with x := y *)
    specialize (normal_form_unique HC HT y y z
                                  (K.multi_refl y) Hmyz Hyn Hzn) as Heq.
    exact Heq.
  Qed.

  (** If y is a normal form of x then every other normal form of x equals y
      and is reachable from y.  The reachability clause is just a restatement
      using [multi_refl]. *)
  Lemma normal_form_properties :
    confluent -> terminating ->
    forall x y z,
      multi x y -> (forall y', ~ step y y') ->
      multi x z -> (forall z', ~ step z z') ->
      multi z y.
  Proof.
    intros HC HT x y z Hxy Hyn Hxz Hzn.
    pose proof (normal_form_unique HC HT x y z Hxy Hxz Hyn Hzn) as Heq.
    subst z.
    destruct (HT x) as [w [Hwy Hwn]].
    (* since z=y, multi z y is just multi y y *)
    apply K.multi_refl.
  Qed.

  (** existence and uniqueness of a normal form of an arbitrary expression
      (combine the earlier two lemmas into the usual ``exists!'' statement). *)
  Definition is_normal x := forall z, ~ step x z.

  Lemma normal_form_unique_exists :
    confluent -> terminating ->
    forall x, exists! y, multi x y /\
                       is_normal y.
  Proof.
    intros HC HT x.
    destruct (normal_form_exists x) as [y [Hy Hyn]].
    exists y; split.
    - split; [assumption|exact Hyn].
    - intros z [Hz Hzn].
        (* any normal form z of x must equal y by uniqueness *)
        eapply normal_form_unique; eauto.
  Qed.

  (** * additional closure and quotient lemmas *)

  Lemma normal_descendant_fixed :
    confluent -> terminating ->
    forall x y z,
      multi x y -> is_normal y -> multi y z -> is_normal z -> y = z.
  Proof.
    intros HC HT x y z Hxy Hyn Hyz Hzn.
    apply normal_fixed_point; assumption.
  Qed.

(** equivalence relation induced by bidirectional reachability *)
Definition equiv (x y : K.Expr) : Prop := multi x y /\ multi y x.

Lemma equiv_refl : forall x, equiv x x.
Proof. intros x; split; apply K.multi_refl. Qed.

Lemma equiv_sym : forall x y, equiv x y -> equiv y x.
Proof. intros x y [Hxy Hyx]; split; assumption. Qed.

Lemma equiv_trans : forall x y z, equiv x y -> equiv y z -> equiv x z.
Proof.
  intros x y z [Hxy Hyx] [Hyz Hzy].
  split.
  - eapply K.multi_trans; eauto.
  - eapply K.multi_trans; eauto.
  Qed.

  Lemma equiv_unique_normal :
    confluent -> terminating ->
    forall x y,
      equiv x y -> is_normal x -> is_normal y -> x = y.
  Proof.
    intros HC HT x y [Hxy Hyx] Hxn Hyn.
  (* both x and y are normal forms of each other *)
  apply normal_form_unique with (x:=x).
  - apply HC.
  - apply HT.
  - apply K.multi_refl.
  - apply Hxy.
  - assumption.
  - assumption.
  Qed.

  (** * normal‑form extraction (quotient map) *)
  Section NormalFunction.
  Context {HC : confluent} {HT : terminating}.

  (** choose a specific normal form using the unique‑existence lemma; we
      use the classical *definite description* operator to obtain a
      value rather than destructing a Prop. *)

  Definition normal (x : K.Expr) : K.Expr :=
    proj1_sig
      (constructive_definite_description
         (fun y : K.Expr => multi x y /\ is_normal y)
         (normal_form_unique_exists HC HT x)).

  Lemma normal_correct :
    forall x, multi x (normal x) /\ is_normal (normal x).
  Proof.
    intro x;
    unfold normal;
    destruct (constructive_definite_description
               (fun y : K.Expr => multi x y /\ is_normal y)
               (normal_form_unique_exists HC HT x)) as [y Hy];
    exact Hy.
  Qed.

  Lemma normal_extensional :
    forall x y, equiv x y -> normal x = normal y.
  Proof.
    intros x y [Hxy Hyx].
    unfold normal.
    destruct (constructive_definite_description
               (fun z : K.Expr => multi x z /\ is_normal z)
               (normal_form_unique_exists HC HT x)) as [nx [Hnx1 Hnx2]].
    destruct (constructive_definite_description
               (fun z : K.Expr => multi y z /\ is_normal z)
               (normal_form_unique_exists HC HT y)) as [ny [Hny1 Hny2]].
    (* both nx and ny are normal forms of x, so they must be equal *)
    assert (Hxy' : multi x ny).
    {
      (* compose x->y and y->ny *)
      eapply K.multi_trans.
      - exact Hxy.
      - exact Hny1.
    }
    assert (nx = ny) as Heq.
    { eapply normal_form_unique; eauto. }
    exact Heq.
  Qed.
  End NormalFunction.

End Phase2_NormalForm.
