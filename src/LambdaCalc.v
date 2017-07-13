
Require Import Nat.
Require Import Arith.


Module Export LambdaCalc.


(* A lambda calculus term using de Bruijn indices. The nat parameter
   indicates the number of bound variables. *)
Inductive lambda (n : nat) : Set :=
  | Var : forall (idx : nat), idx < n -> lambda n
  | Lambda : lambda (S n) -> lambda n
  | Apply : lambda n -> lambda n -> lambda n.


Definition raiseIndex {n : nat} (l : lambda n) : lambda (S n).
  induction l.
  - apply (Var (S n) idx). constructor. exact l.
  - apply Lambda. exact IHl.
  - apply Apply.
    * exact IHl1.
    * exact IHl2.
Defined.


Definition addIndex {n : nat} (depth : nat) (l : lambda n) : lambda (S n).
  induction l.
  - destruct (ltb idx depth).
    * apply raiseIndex. exact (Var n idx l).
    * apply (Var (S n) (S idx)). apply le_n_S. exact l.

  - apply Lambda. exact IHl.

  - apply Apply. exact IHl1. exact IHl2.
Defined.


Fixpoint subst' {n : nat} (depth : nat) (ltD : depth <= n)
  (l : lambda (S n)) (x : lambda n) : lambda n.
  destruct l.

  - destruct (gt_dec idx depth).
    * apply (Var n (pred idx)). unfold gt in g. unfold lt in g.
      destruct idx.
      -- exfalso. inversion g.
      -- simpl. apply le_S_n. exact l.
    * destruct (lt_dec idx depth).
      -- pose (ltN := le_trans (S idx) depth n l0 ltD).
         apply (Var n idx). exact ltN.
      -- exact x.

  - apply Lambda.
    exact (subst' (S n) (S depth) (le_n_S depth n ltD) l (addIndex 0 x)).

  - apply Apply.
    exact (subst' n depth ltD l1 x).
    exact (subst' n depth ltD l2 x).
Defined.

(* Substitutes x into l for the de Bruijn index 0. *)
Definition subst {n : nat} (l : lambda (S n)) (x : lambda n) : lambda n :=
  subst' 0 (le_0_n n) l x.



(* A small step evaluation relationship. *)
Reserved Notation "t1 '/' n '==>' t2" (at level 40).
Inductive step (n : nat) : lambda n -> lambda n -> Prop :=
  | LambdaEval : forall (l l' : lambda (S n)), l / (S n) ==> l'
      -> Lambda n l / n ==> Lambda n l'
  | ApplyEval1 : forall (l1 l2 l1' : lambda n), l1 / n ==> l1'
      -> Apply n l1 l2 / n ==> Apply n l1' l2
  | ApplyEval2 : forall (l1 l2 l2' : lambda n), l2 / n ==> l2'
      -> Apply n l1 l2 / n ==> Apply n l1 l2'
  | ApplyFun : forall (l : lambda (S n)) (x : lambda n),
      (Apply n (Lambda n l) x) / n ==> subst l x
where "t1 '/' n '==>' t2" := (step n t1 t2).

Reserved Notation "t1 '/' n '==>*' t2" (at level 40).
Inductive steps (n : nat) : lambda n -> lambda n -> Prop :=
  | EvalRefl : forall (l : lambda n), steps n l l
  | EvalMany : forall (l1 l2 l3 : lambda n), l1 / n ==> l2
      -> l2 / n ==>* l3 -> l1 / n ==>* l3
where "t1 '/' n '==>*' t2" := (steps n t1 t2).


Theorem lift_step {n : nat} {l l' : lambda n} (s : l / n ==> l')
  : l / n ==>* l'.
Proof.
  apply (EvalMany n l l' l').
  exact s.
  exact (EvalRefl n l').
Qed.

Theorem trans_steps {n : nat} {l1 l2 l3 : lambda n} (evs1 : l1 /n ==>* l2)
  (evs2 : l2 / n ==>* l3) : l1 / n ==>* l3.
Proof.
  induction evs1.
  induction evs2.

  - apply EvalRefl.

  - apply (EvalMany n l1 l2 l3). exact H. exact evs2.

  - apply IHevs1 in evs2. apply (EvalMany n l1 l2 l3). exact H. exact evs2.
Qed.

Theorem lift_lambda {n : nat} {l l' : lambda (S n)}
  (evs : l / (S n) ==>* l') : Lambda n l / n ==>* Lambda n l'.
Proof.
  induction evs.

  - apply EvalRefl.

  - apply LambdaEval in H.
    apply (EvalMany n (Lambda n l1) (Lambda n l2) (Lambda n l3)).
    exact H.
    exact IHevs.
Qed.


Theorem lift_apply {n : nat} {l1 l1' l2 l2' : lambda n}
  (evs1 : l1 / n ==>* l1') (evs2 : l2 / n ==>* l2')
  : Apply n l1 l2 / n ==>* Apply n l1' l2'.
Proof.
  induction evs1.
  induction evs2.

  - apply EvalRefl.

  - apply (ApplyEval2 n l l1 l2) in H.
    apply (EvalMany n (Apply n l l1) (Apply n l l2) (Apply n l l3)).
    exact H.
    exact IHevs2.

  - assert (Apply n l1 l2 / n ==> Apply n l0 l2).
    * apply (ApplyEval1 n l1 l2 l0). exact H.
    * apply (EvalMany n (Apply n l1 l2) (Apply n l0 l2) (Apply n l3 l2')).
      exact H0.
      exact IHevs1.
Qed.

End LambdaCalc.