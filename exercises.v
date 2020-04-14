Set Implicit Arguments.
Require Import List Bool String.
Require Import permutations show.



(* Exercise 123 *)
Definition ex_123_permutation: permutation 5.
Proof.
  refine (let H := (_: permutation_list 5) in plist_to_permutation H).
  pose (1::2::4::3::0::nil) as L. exists L. pose (aux3_reflect 5 L).
  simpl in *. inversion r. auto.
Defined.
Eval compute in show ex_123_permutation.
Eval compute in count_inversions ex_123_permutation.

(* Exercise 124 *)
Definition ex_124_permutation: permutation 6.
Proof.
  refine (let H := (_: permutation_list 6) in plist_to_permutation H).
  pose (5::2::0::1::4::3::nil) as L. exists L. pose (aux3_reflect 6 L).
  simpl in *. inversion r. auto.
Defined.
Eval compute in show ex_124_permutation.
Eval compute in count_inversions ex_124_permutation.

(* Exercise 125 *)
Definition ex_125_permutation: permutation 9.
Proof.
  refine (let H := (_: permutation_list 9) in plist_to_permutation H).
  pose (0::8::5::2::1::4::3::6::7::nil) as L. exists L. pose (aux3_reflect 9 L).
  simpl in *. inversion r. auto.
Defined.
Eval compute in show ex_125_permutation.
Eval compute in count_inversions ex_125_permutation.

(* Exercise 126 *)
Definition ex_126_permutation: permutation 7.
Proof.
  refine (let H := (_: permutation_list 7) in plist_to_permutation H).
  pose (6::4::5::3::0::2::1::nil) as L. exists L. pose (aux3_reflect 7 L).
  simpl in *. inversion r. auto.
Defined.
Eval compute in show ex_126_permutation.
Eval compute in count_inversions ex_126_permutation.



(* Different tests *)
Definition test_permutation: permutation 3.
Proof.
  refine (let H := (_: permutation_list 3) in plist_to_permutation H).
  pose (2::0::1::nil) as L. exists L. pose (aux3_reflect 3 L).
  simpl in *. inversion r. auto.
Defined.
Eval compute in show test_permutation.

Definition inverse_test_permutation: permutation 3.
Proof. exact (inverse_permutation test_permutation). Defined.

Eval compute in show test_permutation.
Eval compute in show (proj1_sig inverse_test_permutation).
Eval compute in show inverse_test_permutation.

Eval compute in show (permutation_mult test_permutation inverse_test_permutation).
