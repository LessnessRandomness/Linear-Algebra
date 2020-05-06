Set Implicit Arguments.
Require Import Arith Omega List Permutation Bool.
Require Import basic_reflect_stuff.

Definition perm n := { L | Permutation L (seq 0 n) }.
Coercion perm_to_list n := fun (p: perm n) => proj1_sig p.

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

Definition permutation_mult n (p1 p2: perm n): perm n.
Proof.
  exists (map (fun i => nth i p1 0) p2).
  assert (Permutation (map (fun i => nth i p1 0) p2) (map (fun i => nth i p1 0) (seq 0 n))).
  { apply Permutation_map. destruct p2. simpl. auto. }
  assert (Permutation (map (fun i => nth i p1 0) (seq 0 n)) p1).
  { pose (full_subsequence p1) as H1. pose (perm_length p1) as H2. rewrite H2 in H1. rewrite H1. apply Permutation_refl. }
  pose (Permutation_trans H H0) as H3. destruct p1. simpl in *. pose (Permutation_trans H3 p). auto.
Qed.

