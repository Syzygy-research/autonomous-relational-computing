Require Import VALIS.Kernel.
Require Import Coq.Logic.Classical.

Module Phase2_Termination (K : KernelSig).
  Definition Expr := K.Expr.
  Definition step := K.step.
  Definition multi := K.multi.
  Definition step_inv (x y : Expr) : Prop := step y x.
  Definition normal_form x := forall y : Expr, ~ step x y.

  (* strong normalization defined via Acc to leverage kernel wf axiom *)
  Definition strongly_normalizing := forall x : Expr, Acc step_inv x.

  Lemma kernel_strong_norm : strongly_normalizing.
  Proof. intros x. apply K.static_termination_wf. Qed.

  Lemma kernel_normal_form_exists :
    forall x, exists y, multi x y /\ normal_form y.
  Proof.
    (* Abstract termination over KernelSig remains open.
       Will be revisited after the concrete model termination proof.
       For now we freeze the lemma and move on to building semantics. *)
    admit.
  Admitted.

  (* proofs are exploratory; admits logged separately *)

End Phase2_Termination.
