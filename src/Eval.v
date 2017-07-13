
Require Import LambdaCalc.
Require Import NormalForm.


Module Export Eval.

(* A function to perform a certain number of evaluations on a lambda term. *)
Fixpoint eval {n : nat} (l : lambda n) : lambda n := match l with
  | Var _ idx ev => Var n idx ev
  | Lambda _ l => Lambda n (eval l)
  | Apply _ l1 l2 => match l1 with
    | Var _ _ _ => Apply n l1 (eval l2)
    | Lambda _ l => subst l l2
    | Apply _ _ _ => Apply n (eval l1) (eval l2)
  end
end.


(* Proof that the eval function transforms a lambda expression through
   a number of evaluation steps. *)
Theorem eval_correspondance {n : nat} (l l' : lambda n) (ev : eval l = l')
  : l / n ==>* l'.
Proof.
  induction l ; inversion ev.

  - simpl. apply EvalRefl.

  - simpl.
    pose (rec := IHl (eval l) eq_refl).
    apply lift_lambda.
    exact rec.

  - induction l1.
    * simpl.
      pose (rec := IHl2 (eval l2) eq_refl).
      apply lift_apply.
      apply EvalRefl.
      exact rec.
    * simpl.
      apply lift_step.
      apply ApplyFun.
    * pose (rec1 := IHl1 (eval (Apply n l1_1 l1_2)) eq_refl).
      pose (rec2 := IHl2 (eval l2) eq_refl).
      simpl in rec1.
      simpl.
      apply lift_apply.
      exact rec1.
      exact rec2.
Qed.


(* Evaluates an expression to normal form. Decreases on i and may
   terminate before finding the normal form (if it exists). *)
Fixpoint evalToNF {n : nat} (i : nat) (l : lambda n) : lambda n.
  destruct i.
  exact l.
 
  destruct (is_nf l).
  - exact l.
  - apply (evalToNF n i).
    apply eval.
    exact l.
Defined.


End Eval.