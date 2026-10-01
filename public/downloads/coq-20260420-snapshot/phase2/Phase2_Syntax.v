Require Import VALIS.Kernel.

Module Phase2_Syntax.

  (*
    Generator-parameterized syntax for algebraic closure.

    This is intentionally minimal:
    - `EUnit` is the unit/identity.
    - `EGen g` embeds a generator `g : Gen`.
    - `EComp` is the binary operation.
  *)
  Section WithGen.
    Context (Gen : Type).

    Inductive Expr : Type :=
    | EUnit
    | EGen (g : Gen)
    | EComp (e1 e2 : Expr).

    (* forbid compositions as immediate right-hand sides (used by some
       Phase-2 operational experiments) *)
    Fixpoint not_comp (e : Expr) : Prop :=
      match e with
      | EComp _ _ => False
      | _ => True
      end.
  End WithGen.

End Phase2_Syntax.
