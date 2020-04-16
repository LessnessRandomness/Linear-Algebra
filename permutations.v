Set Implicit Arguments.
Require Import Arith Omega List Bool.
Require Import basic_reflect_stuff.
Require Export fin.


Definition permutation n := { f: fin n -> fin n | forall y, exists x, f x = y }.
Definition permutation_mult n (p1 p2: permutation n): permutation n.
Proof.
  destruct p1 as [f1 H1], p2 as [f2 H2]. exists (fun x => f2 (f1 x)).
  intros. destruct (H2 y). subst. destruct (H1 x). rewrite <- H.
  exists x0. auto.
Defined.
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

(* Proof idea by olaure01 at coq.discourse.group *)
Theorem permutation_list_length n (p: permutation_list n): length (proj1_sig p) = n.
Proof.
  destruct p as [L [H H0]]. simpl. revert L H H0. induction n.
  + intros. destruct L; auto. simpl in *. assert (n < 0) by (apply H; auto). inversion H1.
  + intros. assert (In n L) by (apply H; auto). destruct (in_split n L H1) as [L1 [L2 H2]].
    subst. apply NoDup_remove in H0. destruct H0 as [H0 H2].
    assert (forall x, In x (L1 ++ L2) <-> x < n).
    - intuition.
      * destruct (H x) as [H4 H5]. assert (In x (L1 ++ n :: L2)).
        { apply in_or_app. simpl. apply in_app_or in H3. tauto. }
        pose (H4 H6) as H7. inversion H7. subst. tauto. auto.
      * assert (x < S n) by intuition. apply H in H4.
        apply in_app_or in H4. simpl in H4. destruct H4 as [H4 | [H5 | H6]].
        ++ apply in_or_app; auto.
        ++ omega.
        ++ apply in_or_app; auto.
    - apply IHn in H3; auto. rewrite app_length. simpl. rewrite app_length in H3. omega.
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

Eval compute in (index 4 (0::1::2::3::4::5::nil) ltac:(intuition) Nat.eq_dec).
Eval compute in (index 3 (0::1::2::3::3::4::nil) ltac:(intuition) Nat.eq_dec).


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

Definition list_of_fins n: list (fin n).
Proof.
  destruct n.
  + exact nil.
  + exact (list_of_fins_partial (exist _ n (le_n _))).
Defined.
Definition list_of_permutation n (p: permutation n) := map (proj1_sig p) (list_of_fins n).

Definition list_of_permutation_thm n (p: permutation n):
  let L := map (fun f: fin n => proj1_sig f) (list_of_permutation p) in
  (forall x, In x L <-> x < n) /\ NoDup L.
Proof.
Admitted.

Definition permutation_to_plist n (p: permutation n): permutation_list n.
Proof.
  exists (map (fun f: fin n => proj1_sig f) (list_of_permutation p)).
  apply list_of_permutation_thm.
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


Definition transposition n := (fin n * fin n)%type.

Definition transpose n (p: permutation n) (t: transposition n): permutation n.
Proof.
  destruct t as [a b]. destruct p as [f p].
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




Definition list_descart_mult A (L1 L2: list A): list (A * A)%type.
Proof.
  induction L1.
  + exact nil.
  + exact (map (fun x => (a, x)) L2 ++ IHL1)%list.
Defined.
Definition all_lt_pairs n: list (fin n * fin n)%type.
Proof.
  pose (list_of_fins n) as L. pose (list_descart_mult L L) as LL.
  pose (fun (p: fin n * fin n) => if le_dec (S (fst p)) (snd p) then true else false) as f.
  exact (filter f LL).
Defined.

Fixpoint count A (f: A -> bool) (L: list A): nat :=
  match L with
  | nil => 0
  | x :: t => let n := count f t in
              if f x then S n else n
  end.

Definition count_inversions n (p: permutation n): nat.
Proof.
  pose (all_lt_pairs n).
  pose (map (fun i => (proj1_sig p (fst i), proj1_sig p (snd i))) l) as l0.
  pose (fun (i: fin n * fin n) => if le_dec (S (snd i)) (fst i) then true else false) as f.
  exact (count f l0).
Defined.


Definition index_of_fin n (p: permutation n): fin n -> fin n.
Proof.
  pose (permutation_to_plist p) as pl. intros [x H].
  pose proof (permutation_list_length pl). destruct pl as [l H1]. assert (In x l). apply H1. auto.
  simpl in *. pose (index x l H2 Nat.eq_dec). exists n0. rewrite <- H0. apply index_length_thm.
Defined.

Theorem aux0 A d (L: list A) y (H: y < length L) (eq_dec: forall (x y: A), {x=y}+{x<>y}): forall H0, index (nth y L d) L H0 eq_dec = y.
Proof. Admitted.

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
Qed.

Definition inverse_permutation n (p: permutation n): permutation n.
Proof.
  pose (index_of_fin p).
  pose (index_of_fin_thm p).
  exists f. exact e.
Defined.








