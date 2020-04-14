Set Implicit Arguments.
Require Import Arith Omega List Bool.

Fixpoint nat_eq_bool (n m: nat): bool :=
  match n, m with
  | O, O => true
  | S n', S m' => nat_eq_bool n' m'
  | _, _ => false
  end.

(* Simplified proof by mwuttke97 from coq.discourse.group *)
Theorem nat_eq_reflect: forall n m, reflect (n = m) (nat_eq_bool n m).
Proof.
  induction n as [| n' H]; intros [| m']; simpl in *.
  + apply ReflectT. auto.
  + apply ReflectF. intuition.
  + apply ReflectF. intuition.
  + destruct (H m') as [IH | IH].
    - apply ReflectT. congruence.
    - apply ReflectF. congruence.
Qed.

Fixpoint le_bool (n m: nat): bool :=
  match n, m with
  | O, _ => true
  | S n', S m' => le_bool n' m'
  | _, _ => false
  end.
Theorem le_reflect: forall n m, reflect (n <= m) (le_bool n m).
Proof.
  induction n as [| n' H]; intros [| m']; simpl in *.
  + apply ReflectT. intuition.
  + apply ReflectT. intuition.
  + apply ReflectF. intuition.
  + destruct (H m') as [IH | IH].
    - apply ReflectT. intuition.
    - apply ReflectF. intuition.
Qed.
Definition lt_bool (n m: nat) := le_bool (S n) m.

Definition In_bool A (x: A) (L: list A) (beq: A -> A -> bool): bool.
Proof.
  induction L.
  + exact false.
  + exact (orb (beq x a) IHL).
Defined.
Theorem In_reflect A (x: A) (L: list A) (beq: A -> A -> bool) (H: forall x y, reflect (x = y) (beq x y)):
    reflect (In x L) (In_bool x L beq).
Proof.
  induction L.
  + simpl. apply ReflectF. auto.
  + simpl. destruct (H a x).
    - subst. assert (beq x x = true). destruct (H x x); auto.
      rewrite H0. simpl. apply ReflectT. left. auto.
    - destruct IHL.
      * replace (beq x a || true) with true by intuition. apply ReflectT. auto.
      * assert (beq x a = false). destruct (H x a); congruence.
        rewrite H0. simpl. apply ReflectF. tauto.
Qed.

Definition NoDup_bool A (L: list A) (beq: A -> A -> bool): bool.
Proof.
  induction L.
  + exact true.
  + exact (negb (In_bool a L beq) && IHL).
Defined.
Theorem NoDup_reflect A (L: list A) (beq: A -> A -> bool) (H: forall x y, reflect (x = y) (beq x y)):
    reflect (NoDup L) (NoDup_bool L beq).
Proof.
  induction L.
  + simpl. apply ReflectT. apply NoDup_nil.
  + simpl. destruct (In_reflect a L _ H).
    - simpl. apply ReflectF. intro. apply NoDup_cons_iff in H0. tauto.
    - simpl. destruct IHL.
      * apply ReflectT. apply NoDup_cons; auto.
      * apply ReflectF. intro. apply NoDup_cons_iff in H0. tauto.
Qed.