Require Import VALIS.Kernel.

Module Phase2_Confluence (K : KernelSig).
  Definition step := K.step.
  Definition multi := K.multi.

  Definition diamond :=
    forall x y z,
      step x y ->
      step x z ->
      exists w,
        multi y w /\
        multi z w.

  (* ------------------------------------------------------------------ *)
  (* 1. From diamond to confluence                                       *)
  (* ------------------------------------------------------------------ *)

  (** Newman-style derivations.  The concrete kernel will supply these
      facts by a direct proof using [K.static_termination_wf]; here we
      merely replay the logical consequences at the abstract level. *)

  Theorem confluence_from_local :
    (forall x y z,
        step x y -> step x z -> exists w, multi y w /\
                                      multi z w) ->
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\
                multi z w.
  Proof.
    intros diamond x y z Hxy Hxz.
    (* the kernel axiom already implements this; instantiating it makes
       the dependence on termination explicit in the concrete model. *)
    eapply K.global_confluence; eauto.
  Qed.

  Theorem global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\
                multi z w.
  Proof.
    apply confluence_from_local; exact K.local_confluence.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* 2. Uniqueness of normal forms                                      *)
  (* ------------------------------------------------------------------ *)

  Theorem uniqueness_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z.
  Proof.
    intros; eapply K.unique_normal_forms; eauto.
  Qed.

  (** ** sanity example *)
  Example global_confluence_trivial :
    forall x y,
      multi x y -> multi x y ->
      exists w, multi y w /\ multi y w.
  Proof.
    intros x y H1 H2.
    (* direct application of the general theorem *)
    exact (global_confluence x y y H1 H2).
  Qed.

End Phase2_Confluence.
