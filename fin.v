Set Implicit Arguments.
Require Import Arith Omega Bool.
Require Import basic_reflect_stuff.


Theorem le_proof_irrelevance: forall n m (p q: le n m), p = q.
Admitted.

Definition fin n := { i | i < n }.
Definition vector A n := fin n -> A.
Definition matrix A n m := fin n -> fin m -> A.
Definition row {A n m} (M: matrix A n m) (i: fin n): vector A m := M i.
Definition col {A n m} (M: matrix A n m) (i: fin m): vector A n := fun x => M x i.

Coercion fin_to_nat n (f: fin n): nat := proj1_sig f.

Theorem fin_eq_reflect n (f1 f2: fin n): reflect (f1 = f2) (nat_eq_bool f1 f2).
Proof.
  destruct f1, f2. simpl. destruct (nat_eq_reflect x x0).
  + apply ReflectT. subst. f_equal. apply le_proof_irrelevance.
  + apply ReflectF. congruence.
Qed.

Theorem fin_lt_reflect n (f1 f2: fin n): reflect (f1 < f2) (lt_bool f1 f2).
Proof.
  destruct f1, f2. simpl. apply le_reflect.
Qed.