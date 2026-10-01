Require Import VALIS.Kernel.

Module Phase2_Base (K : KernelSig).

  (* basic closure definitions and lemmas *)
  Definition multi := K.multi.
  Definition step := K.step.

  Lemma multi_refl : forall x, multi x x.
  Proof.
    unfold multi. apply K.multi_refl.
  Qed.

  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof.
    intros. eapply K.multi_trans; eauto.
  Qed.

  Lemma step_implies_multi : forall x y, step x y -> multi x y.
  Proof.
    intros. apply K.multi_step; assumption.
  Qed.

End Phase2_Base.
