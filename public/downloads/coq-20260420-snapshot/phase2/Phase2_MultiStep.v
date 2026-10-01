Require Import VALIS.Kernel.

Module Phase2_MultiStep (K : KernelSig).
  Definition multi := K.multi.
  Definition step := K.step.

  Lemma multi_step : forall x y z, multi x y -> step y z -> multi x z.
  Proof.
    intros x y z Hxy Hyz.
    eapply K.multi_trans.
    - exact Hxy.
    - apply K.multi_step. exact Hyz.
  Qed.

  Lemma multi_compose : forall x y z, multi x y -> multi y z -> multi x z.
  Proof.
    intros. eapply K.multi_trans; eauto.
  Qed.

  (* deterministic extension lemmas could be added here *)

End Phase2_MultiStep.
