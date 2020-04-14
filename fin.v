Set Implicit Arguments.
Require Import Arith Omega Bool.
Require Import Eqdep_dec.
Require Import Peano_dec.
Require Import basic_reflect_stuff.

(* le_proof_irrelevance proof taken from https://github.com/coq/coq/wiki/Case-Studies#how-to-prove-that-two-proofs-of-n--m-on-nat-are-equal *)
Theorem K_nat (x: nat) (P: x = x -> Prop): P (eq_refl x) -> forall p, P p.
Proof.
  intros. apply K_dec_set with (p := p).
  apply eq_nat_dec. assumption.
Qed.

Theorem eq_rect_eq_nat p (Q: nat -> Type) (x: Q p) (h: p = p): x = eq_rect p Q x p h.
Proof.
  intros. apply K_nat with (p := h). reflexivity.
Qed. 

Scheme le_ind' := Induction for le Sort Prop.

Theorem le_proof_irrelevance: forall n m (p q: le n m), p = q.
Proof.
  induction p using le_ind'; intro q.
  + replace (le_n n) with (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (eq_refl n)) by reflexivity.
    generalize (eq_refl n).
    pattern n at 2 4 6 10, q. case q; [intro | intros m l e].
    - rewrite <- eq_rect_eq_nat. trivial.
    - contradiction (le_Sn_n m). rewrite <- e. assumption.
  + replace (le_S n m p) with (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (eq_refl (S m))) by reflexivity.
    generalize (eq_refl (S m)).
    pattern (S m) at 1 3 4 6, q. case q; [intro Heq | intros m0 l HeqS].
    - contradiction (le_Sn_n m). rewrite Heq. assumption.
    - injection HeqS. intro Heq. generalize l HeqS.
      rewrite <- Heq. intros. rewrite <- eq_rect_eq_nat.
      rewrite (IHp l0). reflexivity.
Qed.


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