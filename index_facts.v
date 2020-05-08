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

Definition index A (dec: eq_dec A) (x: A) (L: list A) (default: nat): nat :=
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

Theorem index_error_some' A (dec: eq_dec A) (x: A) (L: list A) n: index_error dec x L = Some n -> In x L.
Proof.
  intro. eapply index_error_some. exists n. eauto.
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

Theorem index_error_size A (dec: eq_dec A) (x: A) (L: list A): forall n, index_error dec x L = Some n -> n < length L.
Proof.
  induction L; intros.
  + simpl in *. inversion H.
  + unfold index in H. simpl in *. destruct (dec x a).
    - inversion H. omega.
    - destruct (index_error dec x L).
      * inversion H. apply le_n_S. apply IHL. auto.
      * inversion H.
Qed.

(* index facts *)

Theorem index_not_default A (dec: eq_dec A) (L: list A) d x: index dec x L d <> d -> In x L.
Proof.
  induction L; simpl in *; intros.
  + unfold index in H. simpl in H. elim H. auto.
  + unfold index in H. simpl in H. destruct (dec x a). left; congruence. right.
    remember (index_error dec x L) as W. destruct W.
    - symmetry in HeqW. apply index_error_some' in HeqW. auto.
    - elim H. auto.
Qed.

Theorem index_is_default A (dec: eq_dec A) (L: list A) d (H: length L <= d) x: index dec x L d = d -> In x L -> False.
Proof.
  revert d H; induction L; simpl in *; intros.
  + auto.
  + inversion H.
    - subst. clear H. pose proof (IHL (S (length L)) ltac:(auto)). clear IHL.
      unfold index in *. simpl in H0. destruct (dec x a).
      * inversion H0.
      * remember (index_error dec x L) as W. destruct W.
        ++ clear H. destruct H1; try congruence. symmetry in HeqW. apply index_error_size in HeqW. omega.
        ++ clear H0. destruct H1; try congruence. apply H; auto.
    - subst. clear H. assert (length L <= m) by omega. pose proof (IHL m H). clear IHL H2.
      unfold index in *. simpl in H0. destruct (dec x a).
      * inversion H0.
      * destruct (index_error dec x L).
        ++ destruct H1. congruence. inversion H0. apply H3; auto.
        ++ destruct H1. congruence. apply H3; auto.
Qed.

Theorem index_head A (dec: eq_dec A) (x: A) (d: nat) (L: list A): index dec x (x :: L) d = 0.
Proof.
  unfold index. rewrite index_error_head. auto.
Qed.

Theorem index_thm01 A (dec: eq_dec A) (x: A) d (L L': list A) (H: ~ In x L): index dec x (L ++ x :: L') d = length L.
Proof.
  unfold index. revert d. induction L.
  + simpl in *. destruct (dec x x); try congruence.
  + apply not_in_cons in H. destruct H as [H H0]. pose proof (IHL H0). simpl in *. destruct (dec x a); try congruence.
    remember (index_error dec x (L ++ x :: nil)) as W. destruct W.
    * destruct (index_error dec x _). subst; auto. intros. pose (H1 (S (length L))). omega.
    * symmetry in HeqW. rewrite index_error_none in HeqW. exfalso. apply HeqW. apply in_or_app. right. simpl. auto.
Qed.

Theorem index_thm02 A (dec: eq_dec A) x a d (L: list A) (H: In x L) (H0: ~ In a L): index dec x (a :: L) d = S (index dec x L d).
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


(* Proofs that nth and index are kind of inverses of each other *)

Theorem index_nth_id A (dec: eq_dec A) (L: list A) d d' (H: NoDup L) n (H0: n < length L): index dec (nth n L d') L d = n.
Proof.
  revert d n H0. induction L.
  + simpl. intros. inversion H0.
  + simpl in *. destruct n; intros.
    - unfold index. rewrite index_error_head. auto.
    - unfold index. simpl. destruct (dec (nth n L d') a).
      * exfalso. inversion H; subst; clear H. pose proof (IHL H4 (length L) _ (le_S_n _ _ H0)).
        apply H3. clear H3. unfold index in H. remember (index_error dec (nth n L d') L) as W.
        destruct W.
        ++ assert (exists n', index_error dec (nth n L d') L = Some n'). exists n0. congruence.
           apply index_error_some in H1. auto.
        ++ omega.
      * inversion H; subst; clear H. apply le_S_n in H0. pose proof (IHL H4 (S n) n H0).
        unfold index in H. remember (index_error dec (nth n L d') L) as W. destruct W.
        ++ subst. auto.
        ++ omega.
Qed.

Theorem nth_index_id A (dec: eq_dec A) (L: list A) d d' x (H: In x L): nth (index dec x L d) L d' = x.
Proof.
  revert d. induction L.
  + inversion H.
  + simpl in *. unfold index. simpl. destruct (dec x a); try congruence.
    assert (In x L). destruct H; try congruence. pose proof (IHL H0) as H1.
    unfold index in H1. eapply index_error_some with (dec:=dec) in H0.
    destruct (index_error dec x L); auto. destruct H0. inversion H0.
Qed.


(* stuff for inverse permutation *)

Theorem thm00 A x d (L L': list A): nth (length L) (L ++ x :: L') d = x.
Proof.
  induction L; simpl; auto.
Qed.

Theorem thm01 A B d (f: A -> B) (L L': list A): map f L = map (fun n => f (nth n (L ++ L') d)) (seq 0 (length L)).
Proof.
  revert L'. induction L using rev_ind.
  + simpl. auto.
  + simpl. intro. rewrite app_length, seq_app, map_app, map_app. simpl.
    replace ((L ++ x :: nil) ++ L') with (L ++ (x :: L')). rewrite thm00. f_equal.
    rewrite <- IHL. auto.
    { clear IHL. induction L. simpl. auto. simpl. f_equal. auto. }
Qed.

Theorem thm01' A B d (f: A -> B) (L: list A): map f L = map (fun n => f (nth n L d)) (seq 0 (length L)).
Proof.
  replace (fun n => f (nth n L d)) with (fun n => f (nth n (L ++ nil) d)).
  apply thm01. rewrite app_nil_r. auto.
Qed.

Theorem map_ext' A B (L: list A) (f g: A -> B): (forall x, In x L -> f x = g x) -> map f L = map g L.
Proof.
  induction L.
  + simpl. auto.
  + simpl. intros. rewrite H. f_equal; auto. left; auto.
Qed.

Theorem index_of_list_elements A (dec: eq_dec A) (d: nat) (d': A) (L: list A) (H: NoDup L): map (fun i => index dec i L d) L = seq 0 (length L).
Proof.
  replace (map (fun i => index dec i L d) L) with (map (fun n => index dec (nth n L d') L d) (seq 0 (length L))).
  replace (seq 0 (length L)) with (map id (seq 0 (length L))) at 2.
  apply map_ext'. intros. unfold id. rewrite index_nth_id; auto. rewrite in_seq in H0. apply H0.
  + rewrite map_id. auto.
  + symmetry. erewrite thm01'. reflexivity.
Qed.