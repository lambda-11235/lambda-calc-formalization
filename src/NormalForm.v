
Require Import LambdaCalc.

Require Import Decidable.

Module Export NormalForm.


Inductive normal_form (n : nat) : lambda n -> Prop :=
  | VarNF : forall (idx : nat) (ev : idx < n), normal_form n (Var n idx ev)
  | LambdaNF : forall (l : lambda (S n)), normal_form (S n) l
      -> normal_form n (Lambda n l)
  | ApplyVarNF : forall (idx : nat) (ev : idx < n) (l : lambda n),
      normal_form n l -> normal_form n (Apply n (Var n idx ev) l)
  | ApplyApNF : forall (l1 l2 l3 : lambda n), normal_form n (Apply n l1 l2)
      -> normal_form n l3 -> normal_form n (Apply n (Apply n l1 l2) l3).


Theorem sumbool_or (A B : Prop) (ev : {A} + {B}) : A \/ B.
  destruct ev.
  - left. exact a.
  - right. exact b.
Qed.


(* Determines if a a lambda term is in normal form. *)
Theorem is_nf {n : nat} (l : lambda n) : {normal_form n l} + {~ normal_form n l}.
Proof.
  induction l.

  - left. apply VarNF.

  - destruct IHl.
    * left. apply LambdaNF. assumption.
    * right. intro nf. apply n0. inversion nf. assumption.

  - induction l1.
    inversion IHl1.
    inversion IHl2.

    * left. apply ApplyVarNF. exact H0.
    * right. intro nf. inversion nf. apply H0. exact H2.
    * exfalso. apply H. apply VarNF.
    * right. intro nf. inversion nf.
    * inversion IHl1.

      -- inversion IHl2.
         ** left. apply ApplyApNF. exact H. exact H0.
         ** right. intro nf. inversion nf. apply H0. exact H5.
      -- right. intro nf. inversion nf. apply H. exact H2.
Qed.

(* Proof that it is decidable whether a lambda term is in normal form. *)
Theorem dec_nf {n : nat} (l : lambda n) : decidable (normal_form n l).
Proof.
  unfold decidable.
  apply sumbool_or.
  apply is_nf.
Qed.


(* Proof that a term in normal form cannot be evaluated further. *)
Theorem cant_eval_nf {n : nat} {l : lambda n} (nf : normal_form n l)
  : ~(exists (l' : lambda n), l / n ==> l').
Proof.
  induction nf.

  - intro ex. inversion ex. inversion H.

  - intro ex. inversion ex. inversion H.
    apply IHnf.
    exists l'.
    exact H1.

  - intro ex. inversion ex. inversion H.
    * inversion H3.
    * apply IHnf.
      exists l2'.
      exact H3.

  - intro ex. inversion ex. inversion H.
    * apply IHnf1.
      exists l1'.
      exact H3.
    * apply IHnf2.
      exists l2'.
      exact H3.
Qed.


(* Proof that a term not in normal form can be evaluated further. *)
Theorem can_eval_non_nf {n : nat} (l : lambda n) (nnf : ~(normal_form n l))
  : exists (l' : lambda n), l / n ==> l'.
Proof.
  induction l.

  - exfalso. apply nnf. apply VarNF.

  - assert (~ normal_form (S n) l).
    * intro nf. apply nnf. apply LambdaNF in nf. exact nf.
    * apply IHl in H.
      destruct H.
      exists (Lambda n x).
      apply LambdaEval.
      exact H.

  - induction l1.

    * assert (~ normal_form n l2).
      intro nf. apply nnf. apply ApplyVarNF. exact nf.
      apply IHl2 in H.
      destruct H.
      exists (Apply n (Var n idx l) x).
      apply ApplyEval2.
      exact H.

    * exists (subst l1 l2).
      apply ApplyFun.

    * assert (~ (normal_form n (Apply n l1_1 l1_2) /\ normal_form n l2)).

      intro nfs. destruct nfs. apply nnf. apply ApplyApNF.
      exact H. exact H0. 

      apply not_and in H. all: revgoals. apply dec_nf.

      destruct H.
      -- apply IHl1 in H. destruct H.
         exists (Apply n x l2).
         apply ApplyEval1.
         exact H.
      -- apply IHl2 in H. destruct H.
         exists (Apply n (Apply n l1_1 l1_2) x).
         apply ApplyEval2.
         exact H.
Qed.


(* A proof that any term that doesn't contain bound variable and is
   in normal is a lambda abstraction.
   TODO: Change from Fixpoint to Theorem. *)
Fixpoint only_lambda_nf (l : lambda 0) (nf : normal_form 0 l)
  : exists (l' : lambda 1), l = Lambda 0 l'.
Proof.
  destruct l.

  - inversion nf. inversion ev0.

  - exists l. reflexivity.

  - destruct l1.
    destruct nf ; try inversion l.
    * inversion nf.
    * inversion nf.
      pose (rec := only_lambda_nf (Apply 0 l1_1 l1_2) H1).
      destruct rec.
      inversion H4.
Qed.


End NormalForm.