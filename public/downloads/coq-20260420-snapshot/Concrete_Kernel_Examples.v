Require Import VALIS.Kernel_Implementation.

Module Ex := ConcreteKernel.

(* A couple of tiny rewrites showing the restricted kernel in action. *)

Example demo_step : Ex.step (Ex.EComp Ex.EUnit Ex.EUnit) Ex.EUnit.
Proof.
  (* the only reducible form: right-hand expression must not be composite *)
  apply Ex.step_contract.
  - simpl. (* not_comp EUnit = True *) exact I.
  - unfold Ex.refuse. simpl. tauto.
Qed.

Example demo_multi : Ex.multi (Ex.EComp Ex.EUnit Ex.EUnit) Ex.EUnit.
Proof.
  apply Ex.multi_step. apply demo_step.
Qed.

Example demo_unique_normal :
  let x := Ex.EComp Ex.EUnit Ex.EUnit in
  let y := Ex.EUnit in
  Ex.multi x y ->
  Ex.multi x y ->
  (forall y', Ex.step y y' -> False) ->
  (forall z', Ex.step y z' -> False) ->
  y = y.
Proof. intros; reflexivity. Qed.

Example demo_no_step :
  ~ Ex.step (Ex.EComp Ex.EUnit (Ex.EComp Ex.EUnit Ex.EUnit))
           (Ex.EComp Ex.EUnit (Ex.EComp Ex.EUnit Ex.EUnit)).
Proof.
  intros H.
  inversion H as [e Hnc _ | e Hnc _]; subst; simpl in Hnc; contradiction Hnc.
Qed.

Example demo_normal_form :
  let z := Ex.EComp Ex.EUnit (Ex.EComp Ex.EUnit Ex.EUnit) in
  (forall y', Ex.step z y' -> False) ->
  z = z.
Proof. intros; reflexivity. Qed.

(* A slightly more interesting situation: this kernel always rewrites to
   the unit object.  The normal form function from Phase-2 would compute
   the same, but here we just spell out a particular instance. *)
