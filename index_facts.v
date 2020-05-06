Require Import List Omega.
Set Implicit Arguments.

Definition eq_dec A := forall (x y: A), { x = y } + { x <> y }.

Definition index_error A (dec: eq_dec A) (x: A) (L: list A): option nat.
Proof.
  induction L.
  + exact None.
  + destruct (dec x a).
    - exact (Some 0).
    - exact (match IHL with Some n => Some (S n) | None => None end).
Defined.

Definition index A (dec: eq_dec A) (default: nat) (x: A) (L: list A): nat :=
  match (index_error dec x L) with
  | Some n => n
  | None => default
  end.

(* index_error facts *)

Theorem index_error_some A (dec: eq_dec A) (x: A) (L: list A): (exists n, index_error dec x L = Some n) <-> In x L.
Proof.
  split; intros.
  + induction L; intros.
    - simpl in *. destruct H as [x0 H]. inversion H.
    - simpl in *. destruct (dec x a).
      * left. congruence.
      * right. apply IHL. destruct H as [n0 H]. destruct (index_error dec x L).
        ++ exists (n0 - 1). inversion H. f_equal. omega.
        ++ inversion H.
  + induction L.
    - inversion H.
    - simpl. destruct H.
      * subst. destruct (dec x x); try congruence. exists 0. auto.
      * destruct (IHL H) as [n H0]. rewrite H0. destruct (dec x a).
        ++ exists 0. auto.
        ++ exists (S n). auto.
Qed.

Theorem index_error_none A (dec: eq_dec A) (x: A) (L: list A): index_error dec x L = None <-> ~ In x L.
Proof.
  split; intros.
  + intro. rewrite <- index_error_some in H0. destruct H0. rewrite H in H0. inversion H0.
  + induction L.
    - simpl. auto.
    - simpl. apply not_in_cons in H. destruct H. pose (IHL H0) as H1. destruct (dec x a).
      * congruence.
      * destruct (index_error dec x L).
        ++ inversion H1.
        ++ auto.
Qed.

Theorem index_error_head A (dec: eq_dec A) (x: A) (L: list A): index_error dec x (x :: L) = Some 0.
Proof.
  simpl. destruct (dec x x); try congruence.
Qed.

Theorem index_error_size A (dec: eq_dec A) (x: A) (L: list A) (H: In x L): forall n, index_error dec x L = Some n -> n < length L.
Proof.
  induction L; intros.
  + simpl in *. inversion H0.
  + destruct H.
    - subst. rewrite index_error_head in H0. inversion H0. simpl. omega.
    - simpl in *. destruct (dec x a).
      * inversion H0. omega.
      * pose (IHL H) as H1. destruct (index_error dec x L).
        ++ inversion H0. pose (H1 n1 (eq_refl _)). omega.
        ++ inversion H0.
Qed.


(* index facts *)

Theorem index_of_list_elements A (dec: eq_dec A) (d: nat) (L: list A) (H: NoDup L): map (fun i => index dec d i L) L = seq 0 (length L).
Proof.
  induction L using rev_ind.
  - simpl. auto.
  - rewrite app_length. rewrite seq_app. simpl. pose (NoDup_remove_1 _ _ _ H) as H0. rewrite app_nil_r in H0.
    pose (IHL H0) as H1.
Admitted.