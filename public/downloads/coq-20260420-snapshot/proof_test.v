Require Import VALIS.Kernel.
Require Import Coq.micromega.Lia.

Module Test.
  Inductive Expr := EUnit | EComp (a b:Expr).
  Inductive step : Expr -> Expr -> Prop :=
  | step_contract : forall e, step (EComp EUnit e) e.

  Fixpoint size (e : Expr) : nat :=
    match e with
    | EUnit => 1
    | EComp a b => 1 + size a + size b
    end.

  Lemma step_decreases_size :
    forall x y, step x y -> size y < size x.
  Proof.
    intros x y H.
    inversion H; subst; simpl; lia.
  Qed.

  Lemma not_step_self : forall x, ~ step x x.
  Proof.
    intros x H.
    pose proof (step_decreases_size _ _ H) as Hlt.
    lia.
  Qed.

End Test.
