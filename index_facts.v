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

Theorem index_thm01 A (dec: eq_dec A) (x: A) d (L L': list A) (H: ~ In x L): index dec d x (L ++ x :: L') = length L.
Proof.
  unfold index. revert d. induction L.
  + simpl in *. destruct (dec x x); try congruence.
  + apply not_in_cons in H. destruct H as [H H0]. pose proof (IHL H0). simpl in *. destruct (dec x a); try congruence.
    remember (index_error dec x (L ++ x :: nil)) as W. destruct W.
    * destruct (index_error dec x _). subst; auto. intros. pose (H1 (S (length L))). omega.
    * symmetry in HeqW. rewrite index_error_none in HeqW. exfalso. apply HeqW. apply in_or_app. right. simpl. auto.
Qed.

Theorem index_thm02 A (dec: eq_dec A) x a d (L: list A) (H: In x L) (H0: ~ In a L): index dec d x (a :: L) = S (index dec d x L).
Proof.
  induction L.
  + inversion H.
  + rewrite not_in_cons in H0. destruct H0. simpl in *. destruct H.
    - subst. unfold index. simpl. destruct (dec x a); try congruence. destruct (dec x x); try congruence.
    - pose proof (IHL H H1). assert (x <> a). intro. subst. eauto. unfold index. simpl.
      unfold index in H2. simpl in H2. destruct (dec x a); try congruence.
      destruct (dec x a0).
      * auto.
      * destruct (index_error dec x L). auto. auto.
Qed.

Theorem index_thm03 A (dec: eq_dec A) d (L L': list A): map (fun i => index dec d i (L ++ L')) L = map (fun i => index dec d i L) L.
Proof.
Admitted.

Theorem index_of_list_elements A (dec: eq_dec A) (d: nat) (L: list A) (H: NoDup L): map (fun i => index dec d i L) L = seq 0 (length L).
Proof.
  induction L using rev_ind.
  - simpl. auto.
  - rewrite app_length. rewrite seq_app. simpl. pose (NoDup_remove_1 _ _ _ H) as H0. rewrite app_nil_r in H0.
    pose (IHL H0) as H1. rewrite map_app. simpl. rewrite index_thm01. f_equal.
    rewrite index_thm03. auto.
    apply NoDup_remove_2 in H. rewrite app_nil_r in H. auto.
Qed.