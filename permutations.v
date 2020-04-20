Set Implicit Arguments.
Require Import Arith Omega List SetoidList Bool Nat Equivalence Morphisms Setoid.
Require Import basic_reflect_stuff.
Require Export fin.


Definition permutation n := { f: fin n -> fin n | forall y, exists x, f x = y }.
Definition permutation_eq n (p1 p2: permutation n) := forall x, proj1_sig p1 x = proj1_sig p2 x.
Instance PermutationEquiv n: Equivalence (@permutation_eq n).
Proof.
  split.
  + unfold Reflexive. intro. intro. reflexivity.
  + unfold Symmetric. intros. intro. rewrite H. reflexivity.
  + unfold Transitive. intros. intro. rewrite H, H0. reflexivity.
Qed.

Definition permutation_mult n (p1 p2: permutation n): permutation n.
Proof.
  destruct p1 as [f1 H1], p2 as [f2 H2]. exists (fun x => f2 (f1 x)).
  intros. destruct (H2 y). subst. destruct (H1 x). rewrite <- H.
  exists x0. auto.
Defined.
Instance PermutationMultProper n: Proper (@permutation_eq n ==> @permutation_eq n ==> @permutation_eq n) (@permutation_mult n).
Proof.
  intros ? ? ? ? ? ? ?. destruct x, y, x0, y0. simpl in *.
  rewrite H. apply H0.
Qed.

Theorem permutation_mult_assoc n (p1 p2 p3: permutation n):
  permutation_eq (permutation_mult (permutation_mult p1 p2) p3) (permutation_mult p1 (permutation_mult p2 p3)).
Proof.
  intros ?. unfold permutation_mult. destruct p1, p2, p3. simpl. reflexivity.
Qed.

Definition identity_permutation n: permutation n.
Proof.
  exists id. intros y. exists y. reflexivity.
Defined.

Fixpoint permutation_power n (p: permutation n) m :=
  match m with
  | O => identity_permutation n
  | S m' => permutation_mult (permutation_power p m') p
  end.

Definition permutation_list n := { L: list nat | (forall x, In x L <-> x < n) /\ NoDup L }.

(* Proof idea by nojb at coq.discourse.group *)
Theorem permutation_list_length n (p: permutation_list n): length (proj1_sig p) = n.
Proof.
  destruct p as [L [H H0]]. simpl. assert (incl L (seq 0 n)).
  { unfold incl. intros. apply in_seq. simpl. intuition. apply H; auto. }
  assert (incl (seq 0 n) L).
  { unfold incl. intros. apply in_seq in H2. apply H. intuition. }
  pose (seq_NoDup n 0).
  pose (NoDup_incl_length H0 H1).
  pose (NoDup_incl_length n0 H2).
  assert (length L = length (seq 0 n)) by omega.
  rewrite seq_length in H3. auto.
Qed.

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
    reflect ((forall x, In x L <-> x < n) /\ NoDup L) (aux1_bool n L && aux2_bool n L && NoDup_bool L nat_eq_bool).
Proof.
  destruct (aux1_reflect n L).
  + simpl. destruct (aux2_reflect n L).
    - simpl. destruct (NoDup_reflect L _ nat_eq_reflect).
      * apply ReflectT. split; auto. apply aux; auto.
      * apply ReflectF. intro. apply n0. tauto.
    - simpl. apply ReflectF. intro. apply n0. clear n0. destruct H. apply aux in H. tauto.
  + simpl. apply ReflectF. intro. apply n0. clear n0. destruct H. apply aux in H. tauto.
Defined.

Definition index A x (L: list A) (H: In x L) (eq_dec: forall (x y: A), {x=y} + {x<>y}): nat.
Proof.
  induction L.
  + inversion H.
  + destruct (eq_dec x a).
    - exact 0.
    - simpl in H. assert (In x L) by abstract (destruct H; congruence).
      exact (S (IHL H0)).
Defined.

Theorem nth_index_thm A (L: list A) (eq_dec: forall (x y: A), {x=y}+{x<>y}) x d (H: In x L): nth (index x L H eq_dec) L d = x.
Proof.
  induction L.
  + inversion H.
  + simpl in *. destruct (eq_dec x a).
    - congruence.
    - rewrite IHL. auto.
Qed.

Theorem index_length_thm A x (L: list A) (eq_dec: forall (x y: A), {x=y}+{x<>y}) (H: In x L): index x L H eq_dec < length L.
Proof.
  induction L.
  + inversion H.
  + simpl in *. destruct (eq_dec x a).
    - intuition.
    - apply Peano.le_n_S. apply IHL.
Qed.




Definition list_of_fins_partial n (i: fin n): list (fin n).
Proof.
  destruct i. induction x.
  + exact (exist _ 0 l :: nil).
  + assert (x < n) by (apply le_Sn_le; auto). pose (IHx H) as start.
    exact (start ++ (exist _ (S x) l :: nil))%list.
Defined.

Theorem list_of_fins_partial_aux n i (H: S i < n):
  list_of_fins_partial (exist _ (S i) H) = list_of_fins_partial (exist _ i (le_Sn_le _ _ H)) ++ exist _ (S i) H :: nil.
Proof. reflexivity. Qed.

Theorem list_of_fins_partial_length n (i: fin n): length (list_of_fins_partial i) = S i.
Proof.
  destruct i as [i H]. induction i.
  + simpl. auto.
  + assert (i < n) by intuition. rewrite list_of_fins_partial_aux.
    rewrite app_length. rewrite IHi. simpl. omega.
Qed.

Theorem list_of_fins_partial_aux0 n (i: fin n): forall x, In x (list_of_fins_partial i) <-> x <= i.
Proof.
  destruct i as [i H]. induction i.
  + intros. simpl. intuition.
    - destruct x. simpl. injection H1. intros. subst. auto.
    - destruct x. inversion H0. simpl in *. subst. left. f_equal. apply le_proof_irrelevance.
  + intros. rewrite list_of_fins_partial_aux. intuition.
    - apply in_app_or in H0. destruct H0.
      * apply IHi in H0. simpl in *. intuition.
      * destruct H0.
        ++ rewrite H0. auto.
        ++ inversion H0.
    - apply in_or_app. simpl in H0. inversion H0.
      * right. simpl. left. destruct x. simpl in *. subst. f_equal. apply le_proof_irrelevance.
      * clear m H1. simpl in IHi. eapply IHi in H2. left. apply H2.
Qed.

Theorem NoDup_aux A (L: list A) x: NoDup (L ++ x :: nil) <-> NoDup L /\ ~ In x L.
Proof.
  revert x. induction L.
  + simpl. intuition. apply NoDup_nil. apply NoDup_cons. intro H; inversion H. auto.
  + simpl in *. intuition.
    - inversion H; subst; clear H. apply NoDup_cons.
      * intro. apply H2. apply in_or_app. tauto.
      * apply IHL in H3. tauto.
    - subst. inversion H; subst; clear H. apply IHL in H3. destruct H3. apply H2. apply in_or_app.
      right. simpl. tauto.
    - inversion H; subst; clear H. apply IHL in H4. destruct H4. tauto.
    - apply NoDup_cons.
      * intro. inversion H0; subst; clear H0. apply H5; clear H5.
        apply in_app_or in H1. destruct H1; auto. simpl in H0. destruct H0. congruence. elim H0.
      * apply IHL. split. inversion H0; auto. auto.
Qed.

Theorem list_of_fins_partial_NoDup n (i: fin n): NoDup (list_of_fins_partial i).
Proof.
  destruct i as [i H]. induction i.
  + simpl. apply NoDup_cons. intro. inversion H0. apply NoDup_nil.
  + rewrite list_of_fins_partial_aux. apply NoDup_aux. split.
    - apply IHi.
    - intro. pose (list_of_fins_partial_aux0 (exist _ i (le_Sn_le (S i) n H))).
      apply i0 in H0. clear i0. simpl in H0. intuition.
Qed.

Definition list_of_fins n: list (fin n).
Proof.
  destruct n.
  + exact nil.
  + exact (list_of_fins_partial (exist _ n (le_n _))).
Defined.
Theorem list_of_fins_length n: length (list_of_fins n) = n.
Proof.
  destruct n; try reflexivity. unfold list_of_fins.
  apply list_of_fins_partial_length.
Qed.
Theorem list_of_fins_all n: forall x, In x (list_of_fins n).
Proof.
  destruct n.
  + intros [x H]. inversion H.
  + pose proof (list_of_fins_partial_aux0 (exist _ n (le_n (S n)))).
    intros. apply H. simpl. destruct x. simpl. intuition.
Qed.
Theorem list_of_fins_NoDup n: NoDup (list_of_fins n).
Proof.
  destruct n.
  + apply NoDup_nil.
  + apply list_of_fins_partial_NoDup.
Qed. 

Definition list_of_permutation n (p: permutation n) := map (proj1_sig p) (list_of_fins n).

Theorem list_of_permutation_all n (p: permutation n): forall x, In x (list_of_permutation p).
Proof.
  destruct p as [f H]. intro y. destruct (H y). unfold list_of_permutation.
    simpl. subst. apply in_map. unfold list_of_fins. destruct n.
    - destruct x as [x H0]. inversion H0.
    - apply list_of_fins_partial_aux0. destruct x. simpl. intuition.
Qed.
Theorem list_of_permutation_length n (p: permutation n): length (list_of_permutation p) = n.
Proof.
  unfold list_of_permutation. rewrite map_length. apply list_of_fins_length.
Qed.

(* Taken from https://github.com/coq/coq/commit/160ac52f520c5d77cde8fc5734839de54995e165
Will be removed when the lemma is in Standard Library *)
Lemma NoDup_incl_NoDup A (l l' : list A) : NoDup l ->
    length l' <= length l -> incl l l' -> NoDup l'.
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
(* Proof idea by nojb at coq.discourse.group *)
Theorem list_of_permutation_NoDup n (p: permutation n): NoDup (list_of_permutation p).
Proof.
  apply (@NoDup_incl_NoDup _ (list_of_fins n) (list_of_permutation p) (list_of_fins_NoDup n)).
  + pose proof (list_of_permutation_length p).
    pose proof (list_of_fins_length n).
    rewrite H, H0. apply le_n.
  + intros ? ?. apply list_of_permutation_all.
Qed.

Definition list_of_permutation_thm0 n (p: permutation n):
  let L := map (fun (f: fin n) => proj1_sig f) (list_of_permutation p) in
  (forall x, In x L <-> x < n) /\ NoDup L.
Proof.
  intros. split.
  + intuition.
    - induction (list_of_permutation p).
      * inversion H.
      * simpl in *. destruct H.
        ++ destruct a. simpl in *. subst. auto.
        ++ apply IHl. exact H.
    - pose proof (list_of_permutation_all p). pose proof (H0 (exist _ x H)). unfold L.
      clear L H0. induction (list_of_permutation p).
      * inversion H1.
      * simpl in *. destruct H1.
        ++ destruct a. simpl in *. left. congruence.
        ++ right. apply (IHl H0).
  + pose proof (list_of_permutation_NoDup p). unfold L. clear L.
    induction (list_of_permutation p).
    - apply NoDup_nil.
    - inversion H; subst; clear H. simpl. apply NoDup_cons.
      * intro. apply H2. clear IHl H2 H3. induction l.
        ++ inversion H.
        ++ simpl in *. destruct H.
          -- left. destruct a, a0. simpl in *. subst. f_equal. apply le_proof_irrelevance.
          -- right. eauto.
      * eauto.
Qed.

Definition permutation_to_plist n (p: permutation n): permutation_list n.
Proof.
  exists (map (fun f: fin n => proj1_sig f) (list_of_permutation p)).
  pose proof (list_of_permutation_thm0 p). apply H.
Defined.


(* Fixed definition by kyod from coq.discourse.group *)
Definition plist_to_permutation_aux n (pl: permutation_list n): fin n -> fin n.
Proof.
  pose (permutation_list_length pl) as H.
  intros [i H0]. destruct pl as [l H12].
  exists (nth i l 0).
  simpl in H. destruct H12 as [H1 H2]. assert (In i l) by (apply H1; auto). apply H1. apply nth_In. rewrite H. auto.
Defined.

Theorem plist_to_permutation_aux_thm n (pl: permutation_list n): forall y, exists x, plist_to_permutation_aux pl x = y.
Proof.
  intros [x H]. pose proof (permutation_list_length pl). destruct pl as [l H1]. assert (In x l). apply H1. auto.
  simpl in *. pose (index x l H2 Nat.eq_dec). assert (n0 < n).
  rewrite <- H0. apply index_length_thm.
  exists (exist _ n0 H3). simpl.
  assert (forall n (f1 f2: fin n), proj1_sig f1 = proj1_sig f2 -> f1 = f2).
    intros. destruct f1, f2. simpl in *. subst. apply f_equal. apply le_proof_irrelevance.
  apply H4. simpl. unfold n0. apply nth_index_thm.
Qed.

Definition plist_to_permutation {n} (pl: permutation_list n): permutation n.
Proof.
  exists (plist_to_permutation_aux pl). apply plist_to_permutation_aux_thm.
Defined.


Definition transposition n := { p: fin n * fin n | fst p < snd p }.

Definition transpose n (p: permutation n) (t: transposition n): permutation n.
Proof.
  destruct t as [[a b] H]. destruct p as [f p].
  exists (fun (x: fin n) => if nat_eq_bool a x then f b else if nat_eq_bool b x then f a else f x).
  intros. destruct (fin_eq_reflect (f b) y).
  + exists a. destruct (fin_eq_reflect a a); auto. exfalso; auto.
  + destruct (fin_eq_reflect (f a) y).
    - subst. assert (a <> b). intro. subst. auto. exists b.
      destruct (fin_eq_reflect a b); subst; auto.
      destruct (fin_eq_reflect b b); auto. exfalso. auto.
    - pose (p y). destruct e. exists x. subst.
      assert (a <> x). congruence. assert (b <> x). congruence.
      destruct (fin_eq_reflect a x). subst. exfalso. auto.
      destruct (fin_eq_reflect b x). subst. exfalso. auto.
      auto.
Defined.

Definition transpositions_added_to_permutation n (start: permutation n) (L: list (transposition n)): permutation n.
Proof.
  revert start. induction L.
  + intro. exact start.
  + intro. exact (IHL (transpose start a)).
Defined.

Definition transpositions_to_permutation n (L: list (transposition n)): permutation n :=
  transpositions_added_to_permutation (identity_permutation n) L.

Theorem nil_to_permutation n: permutation_eq (transpositions_to_permutation nil) (identity_permutation n).
Proof.
  intros ?. simpl. auto.
Qed.


Definition all_lt_pairs n: list (fin n * fin n)%type.
Proof.
  pose (list_of_fins n) as L. pose (list_prod L L) as LL.
  pose (fun (p: fin n * fin n) => if lt_bool (fst p) (snd p) then true else false) as f.
  exact (filter f LL).
Defined.

Definition count A (f: A -> bool) (L: list A): nat := length (filter f L).

Definition count_inversions n (p: permutation n): nat.
Proof.
  pose (all_lt_pairs n).
  pose (map (fun (pair: fin n * fin n) => match pair with (f1, f2) => (proj1_sig p f1, proj1_sig p f2) end) l).
  exact (count (fun (pair: fin n * fin n) => match pair with (f1, f2) => lt_bool f2 f1 end) l0).
Defined.
Instance CountInversionsProper n: Proper (@permutation_eq n ==> eq) (@count_inversions n).
Proof.
  intros ? ? ?. destruct x, y. compute in H. unfold count_inversions.
  simpl. induction (all_lt_pairs).
  + unfold count. simpl. auto.
  + simpl. unfold count in *. simpl. destruct a.
    repeat rewrite H. destruct (lt_bool (x0 f0) (x0 f)).
    - simpl. f_equal. apply IHl.
    - apply IHl.
Qed.

Definition parity_of_permutation n (p: permutation n) := even (count_inversions p).
Instance ParityOfPermutationProper n: Proper (@permutation_eq n ==> eq) (@parity_of_permutation n).
Proof.
  intros ? ? ?. unfold parity_of_permutation. rewrite H. auto.
Qed.


Theorem transposition_changes_parity n (p: permutation n) (t: transposition n):
  parity_of_permutation (transpose p t) = negb (parity_of_permutation p).
Proof.
Admitted.

Theorem all_lt_pairs_lt n: forall x, In x (all_lt_pairs n) -> fst x < snd x.
Proof.
  intros [f1 f2] H. simpl. unfold all_lt_pairs in *. rewrite filter_In in H.
  destruct H. simpl in *. pose proof (fin_lt_reflect f1 f2). destruct (lt_bool f1 f2).
  + inversion H1. auto.
  + inversion H0.
Qed.

Theorem inversions_of_identity_permutation n: count_inversions (identity_permutation n) = 0.
Proof.
  unfold count_inversions, identity_permutation, id. pose proof (@all_lt_pairs_lt n). simpl.
  induction (all_lt_pairs n).
  + compute. auto.
  + simpl. unfold count. simpl in *. destruct a. pose proof (fin_lt_reflect f0 f). inversion H0.
    - pose (H (f, f0)). exfalso. simpl in *. assert (f < f0). auto. omega.
    - unfold count in IHl. rewrite IHl. auto. intros. apply H. auto.
Qed.

Theorem parity_of_identity_permutation n: parity_of_permutation (identity_permutation n) = true.
Proof.
  unfold parity_of_permutation. rewrite inversions_of_identity_permutation. simpl. auto.
Qed.

Theorem unique_parity_of_transposition_list n (p: permutation n):
  forall L, permutation_eq p (transpositions_to_permutation L) -> parity_of_permutation p = even (length L).
Proof.
Admitted.


Definition index_of_fin n (p: permutation n): fin n -> fin n.
Proof.
  pose (permutation_to_plist p) as pl. intros [x H].
  pose proof (permutation_list_length pl). destruct pl as [l H1]. assert (In x l). apply H1. auto.
  simpl in *. pose (index x l H2 Nat.eq_dec). exists n0. rewrite <- H0. apply index_length_thm.
Defined.

Theorem aux0 A d (L: list A) y (H: y < length L) (H0: NoDup L) (eq_dec: forall (x y: A), {x=y}+{x<>y}): forall H0, index (nth y L d) L H0 eq_dec = y.
Proof.
  revert y H. induction L.
  + simpl. tauto.
  + simpl in *. destruct y.
    - intros. destruct eq_dec. auto. elim n; auto.
    - intros. destruct eq_dec.
      * exfalso. destruct H1. 
        ++ inversion H0; subst; clear H0. clear e. pose (@nth_In A y L d).
           assert (y < length L) by intuition. pose (i H0). tauto.
        ++ inversion H0; subst; clear H0. tauto.
      * f_equal. apply IHL. inversion H0; auto. intuition.
Qed.


Theorem index_of_fin_thm n (p: permutation n): forall y, exists x, index_of_fin p x = y.
Proof.
  unfold index_of_fin. intros [y H]. pose (nth y (proj1_sig (permutation_to_plist p)) 0).
  assert (length (proj1_sig (permutation_to_plist p)) = n).
    unfold permutation_to_plist. simpl. rewrite map_length.
    unfold list_of_permutation. rewrite map_length.
    unfold list_of_fins. destruct n; auto.
    apply list_of_fins_partial_length.
  assert (y < length (proj1_sig (permutation_to_plist p))) by (rewrite H0; auto).
  assert (In n0 (proj1_sig (permutation_to_plist p))) by (apply nth_In; auto).
  assert (n0 < n).
    unfold permutation_to_plist in H2. simpl in H2.
    apply in_map_iff in H2. destruct H2 as [[x H2] [H3 H4]].
    simpl in H3. congruence.
  exists (exist _ n0 H3).
  assert (forall n (f1 f2: fin n), proj1_sig f1 = proj1_sig f2 -> f1 = f2) as H4.
    intros. destruct f1, f2. simpl in *. subst. apply f_equal. apply le_proof_irrelevance.
  apply H4. unfold n0. simpl. apply aux0. apply H1.
  pose proof (list_of_permutation_NoDup p). clear n0 H0 H1 H2 H3 H4 H y. induction (list_of_permutation p).
    apply NoDup_nil.
    rewrite map_cons. apply NoDup_cons.
      intro. inversion H5; subst. pose (IHl H3). apply H2. clear H5 IHl H2 H3 n0. induction l.
        inversion H. simpl in *. destruct H.
          left. destruct a0, a. simpl in H. subst. f_equal. apply le_proof_irrelevance.
          right. auto.
        inversion H5; subst. auto.
Qed.

Definition inverse_permutation n (p: permutation n): permutation n.
Proof.
  pose (index_of_fin p).
  pose (index_of_fin_thm p).
  exists f. exact e.
Defined.


Theorem permutation_mult_inverse_is_id n (p: permutation n): permutation_eq (permutation_mult p (inverse_permutation p)) (identity_permutation n).
Proof.
  unfold permutation_eq. intro. simpl. unfold id.
  unfold permutation_mult. destruct p as [p H]. simpl.
Admitted.


Definition list_of_all_permutations n: { L: list (permutation n) | (forall x, InA (@permutation_eq n) x L) /\ NoDupA (@permutation_eq n) L }.
Proof.
Admitted.



