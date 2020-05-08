Set Implicit Arguments.
Require Import Arith Omega List Permutation Bool.
Require Import index_facts basic_reflect_stuff.

Definition perm n := { L | Permutation L (seq 0 n) }.
Coercion perm_to_list n := fun (p: perm n) => proj1_sig p.
Definition perm_eq n (p1 p2: perm n) := @eq (list nat) p1 p2.

Definition perm_id n: perm n.
Proof.
  exists (seq 0 n). apply Permutation_refl.
Defined.

Definition perm_length n (p: perm n): length p = n.
Proof.
  destruct p. simpl. apply Permutation_length in p. rewrite seq_length in p. auto.
Qed.
 
(* Taken from https://github.com/coq/coq/commit/160ac52f520c5d77cde8fc5734839de54995e165
Will be removed when the corrected lemma NoDup_Permutation_bis is in Standard Library *)
Lemma NoDup_incl_NoDup A (l l' : list A) : NoDup l -> length l' <= length l -> incl l l' -> NoDup l'.
Proof.
  revert l'; induction l; simpl; intros l' Hnd Hlen Hincl.
  - now destruct l'; inversion Hlen.
  - assert (In a l') as Ha by now apply Hincl; left.
    apply in_split in Ha as [l1' [l2' ->]].
    inversion_clear Hnd as [|? ? Hnin Hnd'].
    apply (NoDup_Add (Add_app a l1' l2')); split.
    + apply IHl; auto.
      * rewrite app_length.
        rewrite app_length in Hlen; simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
        now apply Nat.succ_le_mono.
      * apply incl_Add_inv with (u:= l1' ++ l2') in Hincl; auto.
        apply Add_app.
    + intros Hnin'.
      assert (incl (a :: l) (l1' ++ l2')) as Hincl''.
      { apply incl_tran with (l1' ++ a :: l2'); auto.
        intros x Hin.
        apply in_app_or in Hin as [Hin|[->|Hin]]; intuition. }
      apply NoDup_incl_length in Hincl''; [ | now constructor ].
      apply (Nat.nle_succ_diag_l (length l1' + length l2')).
      rewrite_all app_length.
      simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
      now transitivity (S (length l)).
Qed.

Lemma NoDup_Permutation_bis A (l l' : list A) : NoDup l ->
  length l' <= length l -> incl l l' -> Permutation l l'.
Proof.
 intros. apply NoDup_Permutation; auto.
 - now apply NoDup_incl_NoDup with l.
 - split; auto.
   apply NoDup_length_incl; trivial.
Qed.

Theorem perm_condition_iff n L: Permutation L (seq 0 n) <-> ((forall x, In x L <-> x < n) /\ NoDup L).
Proof.
  intuition.
  + pose (Permutation_in _ H H0) as H1. rewrite in_seq in H1. apply H1.
  + assert (0 <= x < 0 + n) as H1 by omega. apply in_seq in H1. pose (Permutation_in _ (Permutation_sym H) H1). auto.
  + apply Permutation_sym in H. apply Permutation_NoDup in H; auto. apply seq_NoDup.
  + eapply NoDup_Permutation_bis in H1.
    - exact H1.
    - apply NoDup_incl_length.
      * apply seq_NoDup.
      * intros ? ?. rewrite in_seq in H. destruct H. apply H0 in H2. auto.
    - intros ? ?. apply H0 in H. apply in_seq. omega.
Qed.

Theorem full_subsequence (L: list nat): map (fun i => nth i L 0) (seq 0 (length L)) = L.
Proof.
  induction L using rev_ind.
  + simpl. auto.
  + rewrite app_length. rewrite seq_app. rewrite map_app.
    simpl. rewrite app_nth2.
    - rewrite PeanoNat.Nat.sub_diag. rewrite <- IHL at 2. simpl. f_equal.
      apply map_ext_in. intros. apply app_nth1. apply in_seq in H. simpl in H. tauto.
    - apply le_n.
Qed.

Definition perm_mult n (p1 p2: perm n): perm n.
Proof.
  exists (map (fun i => nth i p1 0) p2).
  assert (Permutation (map (fun i => nth i p1 0) p2) (map (fun i => nth i p1 0) (seq 0 n))).
  { apply Permutation_map. destruct p2. simpl. auto. }
  assert (Permutation (map (fun i => nth i p1 0) (seq 0 n)) p1).
  { pose (full_subsequence p1) as H1. pose (perm_length p1) as H2. rewrite H2 in H1. rewrite H1. apply Permutation_refl. }
  pose (Permutation_trans H H0) as H3. destruct p1. simpl in *. pose (Permutation_trans H3 p). auto.
Defined.

Theorem perm_mult_assoc n (p1 p2 p3: perm n): perm_eq (perm_mult (perm_mult p1 p2) p3) (perm_mult p1 (perm_mult p2 p3)).
Proof.
  pose proof (perm_length p1). pose proof (perm_length p2). pose proof (perm_length p3).
  destruct p1, p2, p3. simpl in *. unfold perm_mult, perm_eq. simpl. rewrite map_map.
  apply map_ext'. intros i H2.
  apply perm_condition_iff in p1. destruct p1. pose proof (proj1 (H3 _) H2).
  assert (forall x, x < n -> In x x1). intros. apply H3. auto.
  clear p0 p H3. clear H H1. revert n H0 H5 H6. revert i H2. induction x0.
  + simpl. intros. omega.
  + simpl. intros. destruct i. auto. eapply IHx0. apply H6. omega.
    assert (length x0 = n - 1) by omega. exact H. omega. intros.
    apply H6. omega.
Qed.


Theorem perm_mult_id n (p: perm n): perm_eq (perm_mult p (perm_id n)) p.
Proof.
  pose proof (perm_length p).
  destruct p. unfold perm_eq, perm_mult, perm_id. simpl in *. rewrite <- H.
  apply full_subsequence.
Qed.

Theorem id_mult_perm n (p: perm n): perm_eq (perm_mult (perm_id n) p) p.
Proof.
  pose proof (perm_length p). destruct p. simpl in *.
  pose proof (proj1 (perm_condition_iff _ _) p). destruct H0.
  assert (forall x0, In x0 x -> x0 < n). intuition. apply H0. auto.
  unfold perm_eq, perm_mult, perm_id. simpl in *.
  (* map (fun i : nat => nth i (seq 0 n) 0) x = x *)
  clear p H H0 H1. induction x.
  + simpl. auto.
  + simpl in *. assert (a < n). apply H2. auto. rewrite IHx. f_equal.
    rewrite seq_nth. auto. auto.
    intros. apply H2. auto.
Qed.


Definition perm_inv n (p: perm n): perm n.
Proof.
  pose proof (perm_length p). exists (map (fun i => index Nat.eq_dec i p 0) (seq 0 n)).
  destruct p. simpl in *. pose proof (perm_condition_iff n x). pose proof (proj1 H0 p). destruct H1. clear H1 H0.
  assert (Permutation (map (fun i => index Nat.eq_dec i x 0) x) (map (fun i => index Nat.eq_dec i x 0) (seq 0 n))).
  { apply Permutation_map. auto. }
  rewrite index_of_list_elements in H0; eauto. rewrite H in H0. apply Permutation_sym; auto.
Defined.

Theorem perm_mult_perm_inv_id n (p: perm n): perm_eq (perm_mult p (perm_inv p)) (perm_id n).
Proof.
  destruct p. unfold perm_eq, perm_mult, perm_inv, perm_id. simpl. rewrite map_map.
  replace (seq 0 n) with (map id (seq 0 n)) at 2 by (apply map_id).
  apply map_ext'. intros. rewrite nth_index_id. unfold id; auto. apply Permutation_sym in p.
  eapply Permutation_in; eauto.
Qed.

Theorem perm_inv_mult_perm_id n (p: perm n): perm_eq (perm_mult (perm_inv p) p) (perm_id n).
Proof.
  pose proof (perm_length p) as H. destruct p. unfold perm_eq, perm_mult, perm_inv, perm_id. simpl in *.
  apply perm_condition_iff in p. destruct p as [H0 H1].
  assert (forall t, In t x -> nth t (map (fun i0 => index Nat.eq_dec i0 x 0) (seq 0 n)) 0 = 
                    let f := fun i0 => index Nat.eq_dec i0 x 0 in f (nth t (seq 0 n) 0)).
  { intros. rewrite <- (map_nth _ (seq 0 n) _ _). apply nth_indep. rewrite map_length.
    rewrite seq_length. apply H0. auto. }
  simpl in H1. assert (forall t, In t x -> index Nat.eq_dec (nth t (seq 0 n) 0) x 0 = index Nat.eq_dec t x 0).
  { intros. apply H0 in H3. rewrite seq_nth. auto. auto. }
  assert (forall t, In t x -> nth t (map (fun i0 : nat => index Nat.eq_dec i0 x 0) (seq 0 n)) 0 = index Nat.eq_dec t x 0).
  { intros. rewrite H2. simpl. rewrite H3. auto. auto. auto. }
  clear H2.
  assert (map (fun i => nth i (map (fun i0 => index Nat.eq_dec i0 x 0) (seq 0 n)) 0) x = map (fun i => index Nat.eq_dec i x 0) x).
  { apply map_ext'. auto. }
  rewrite H2. rewrite index_of_list_elements. rewrite H. auto. auto. auto.
Qed.

(* Reflect stuff *)

Theorem aux n (L: list nat): (forall x, In x L <-> x < n) <-> ((forall x, In x L -> x < n) /\ (forall x, x < n -> In x L)).
Proof.
  split; intros.
  + split; intros. 
    - apply H. auto.
    - apply H. auto.
  + destruct H. split; intros.
    - apply H. auto.
    - apply H0. auto.
Qed.

Definition aux1_bool (n: nat) (L: list nat): bool.
Proof.
  induction L.
  + exact true.
  + exact (if le_bool (S a) n then IHL else false).
Defined.
Theorem aux1_reflect (n: nat) (L: list nat): reflect (forall x, In x L -> x < n) (aux1_bool n L).
Proof.
  induction L.
  + simpl. apply ReflectT. tauto.
  + simpl. destruct n.
    - apply ReflectF. intro. assert (a < 0). apply H. left. auto. inversion H0.
    - destruct (le_reflect a n).
      * destruct IHL.
        ++ apply ReflectT. intros. destruct H.
          -- subst. intuition.
          -- apply l0. auto.
        ++ apply ReflectF. intro. apply n0. intros. apply H. auto.
      * apply ReflectF. intro. apply n0. assert (a < S n).
        apply H. auto. intuition.
Qed.

(* Simplified definition by mwuttke97 from coq.discourse.group *)
Definition aux2_bool (n : nat) (L: list nat) :=
  forallb (fun x => In_bool x L nat_eq_bool) (seq 0 n).

(* Proof by mwuttke97 from coq.discourse.group *)
Lemma forallb_reflect (X : Type) (f : X -> bool) (xs : list X) :
  reflect (forall x, In x xs -> f x = true) (forallb f xs).
Proof.
  induction xs.
  - cbn. left. tauto.
  - cbn. destruct (f a) eqn:E; cbn.
    + destruct IHxs.
      * left. intros x [-> | H]; auto.
      * right. intuition.
    + right. intros H. specialize (H a (or_introl eq_refl)). congruence.
Qed.

(* Proof by mwuttke97 from coq.discourse.group *)
Theorem aux2_reflect (n: nat) (L: list nat): reflect (forall x, x < n -> In x L) (aux2_bool n L).
Proof.
  unfold aux2_bool.
  pose proof forallb_reflect (fun x => In_bool x L nat_eq_bool) (seq 0 n) as [H|H].
  - left. intros x Hx.
    assert (In x (seq 0 n)) as Haux.
    { replace x with (x + 0) by omega. apply in_seq. omega. }
    specialize H with (1 := Haux).
    rewrite reflect_iff; eauto.
    apply In_reflect. intros. apply nat_eq_reflect.
  - right. intros H'. contradict H.
    intros x Hx.
    assert (x < n) as Haux.
    { apply in_seq in Hx. omega. }
    specialize H' with (1 := Haux).
    rewrite reflect_iff in H'; eauto.
    apply In_reflect. intros. apply nat_eq_reflect.
Qed.

Theorem aux3_reflect (n: nat) (L: list nat):
    reflect (Permutation L (seq 0 n)) (aux1_bool n L && aux2_bool n L && NoDup_bool L nat_eq_bool).
Proof.
  destruct (aux1_reflect n L).
  + simpl. destruct (aux2_reflect n L).
    - simpl. destruct (NoDup_reflect L _ nat_eq_reflect).
      * apply ReflectT. rewrite perm_condition_iff. split; auto. apply aux; auto.
      * apply ReflectF. intro. apply n0. rewrite perm_condition_iff in H. tauto.
    - simpl. apply ReflectF. intro. apply n0. clear n0.
      rewrite perm_condition_iff in H. destruct H. apply aux in H. tauto.
  + simpl. apply ReflectF. intro. apply n0. clear n0.
    rewrite perm_condition_iff in H. destruct H. apply aux in H. tauto.
Defined.

