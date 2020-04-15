Set Implicit Arguments.
Require Import List Bool String.
Require Import permutations show.



(* Exercise 123 *)
Definition ex_123_permutation: permutation 5.
Proof.
  refine (let H := (_: permutation_list 5) in plist_to_permutation H).
  pose (1::2::4::3::0::nil) as L. exists L. pose (aux3_reflect 5 L).
  inversion r. auto.
Defined.
Eval compute in show ex_123_permutation.
Eval compute in count_inversions ex_123_permutation.

(* Exercise 124 *)
Definition ex_124_permutation: permutation 6.
Proof.
  refine (let H := (_: permutation_list 6) in plist_to_permutation H).
  pose (5::2::0::1::4::3::nil) as L. exists L. pose (aux3_reflect 6 L).
  inversion r. auto.
Defined.
Eval compute in show ex_124_permutation.
Eval compute in count_inversions ex_124_permutation.

(* Exercise 125 *)
Definition ex_125_permutation: permutation 9.
Proof.
  refine (let H := (_: permutation_list 9) in plist_to_permutation H).
  pose (0::8::5::2::1::4::3::6::7::nil) as L. exists L. pose (aux3_reflect 9 L).
  inversion r. auto.
Defined.
Eval compute in show ex_125_permutation.
Eval compute in count_inversions ex_125_permutation.

(* Exercise 126 *)
Definition ex_126_permutation: permutation 7.
Proof.
  refine (let H := (_: permutation_list 7) in plist_to_permutation H).
  pose (6::4::5::3::0::2::1::nil) as L. exists L. pose (aux3_reflect 7 L).
  inversion r. auto.
Defined.
Eval compute in show ex_126_permutation.
Eval compute in count_inversions ex_126_permutation.

(* Exercise 169 *)
Definition ex_169_permutation_1: permutation 4.
Proof.
  refine (let H := (_: permutation_list 4) in plist_to_permutation H).
  pose (3::0::2::1::nil) as L. exists L. pose (aux3_reflect 4 L).
  inversion r. auto.
Defined.
Definition ex_169_permutation_2: permutation 4.
Proof.
  refine (let H := (_: permutation_list 4) in plist_to_permutation H).
  pose (2::1::3::0::nil) as L. exists L. pose (aux3_reflect 4 L).
  inversion r. auto.
Defined.
Definition ex_169_result := permutation_mult ex_169_permutation_1 ex_169_permutation_2.
Eval compute in show ex_169_permutation_1.
Eval compute in show ex_169_permutation_2.
Eval compute in show ex_169_result.

(* Exercise 170 *)
Definition ex_170_permutation_1: permutation 5.
Proof.
  refine (let H := (_: permutation_list 5) in plist_to_permutation H).
  pose (1::3::4::0::2::nil) as L. exists L. pose (aux3_reflect 5 L).
  inversion r. auto.
Defined.
Definition ex_170_permutation_2: permutation 5.
Proof.
  refine (let H := (_: permutation_list 5) in plist_to_permutation H).
  pose (4::2::3::0::1::nil) as L. exists L. pose (aux3_reflect 5 L).
  inversion r. auto.
Defined.
Definition ex_170_result := permutation_mult ex_170_permutation_1 ex_170_permutation_2.
Eval compute in show ex_170_permutation_1.
Eval compute in show ex_170_permutation_2.
Eval compute in show ex_170_result.

(* Exercise 171 *)
Definition ex_171_permutation_1: permutation 5.
Proof.
  refine (let H := (_: permutation_list 5) in plist_to_permutation H).
  pose (2::4::0::1::3::nil) as L. exists L. pose (aux3_reflect 5 L).
  inversion r. auto.
Defined.
Definition ex_171_permutation_2: permutation 5.
Proof.
  refine (let H := (_: permutation_list 5) in plist_to_permutation H).
  pose (2::3::0::4::1::nil) as L. exists L. pose (aux3_reflect 5 L).
  inversion r. auto.
Defined.
Definition ex_171_result := permutation_mult ex_171_permutation_1 ex_171_permutation_2.
Eval compute in show ex_171_permutation_1.
Eval compute in show ex_171_permutation_2.
Eval compute in show ex_171_result.

(* Exercise 172 *)
Definition ex_172_permutation: permutation 4.
Proof.
  refine (let H := (_: permutation_list 4) in plist_to_permutation H).
  pose (1::2::3::0::nil) as L. exists L. pose (aux3_reflect 4 L).
  inversion r. auto.
Defined.
Definition ex_172_result := permutation_power ex_172_permutation 2.
Eval compute in show ex_172_permutation.
Eval compute in show ex_172_result.

(* Exercise 173 *)
Definition ex_173_permutation: permutation 5.
Proof.
  refine (let H := (_: permutation_list 5) in plist_to_permutation H).
  pose (2::3::4::0::1::nil) as L. exists L. pose (aux3_reflect 5 L).
  inversion r. auto.
Defined.
Definition ex_173_result := permutation_power ex_173_permutation 3.
Eval compute in show ex_173_permutation.
Eval compute in show ex_173_result.

(* Exercise 176 *)
Definition ex_176_permutation: permutation 10.
Proof.
  refine (let H := (_: permutation_list 10) in plist_to_permutation H).
  pose (2::4::3::0::6::9::1::5::8::7::nil) as L. exists L. pose (aux3_reflect 10 L).
  inversion r. auto.
Defined.
Definition ex_176_result_naive := permutation_power ex_176_permutation 100.
Eval compute in show ex_176_permutation.
Eval compute in show ex_176_result_naive.

(* Exercise 177 *)
Definition ex_177_permutation: permutation 10.
Proof.
  refine (let H := (_: permutation_list 10) in plist_to_permutation H).
  pose (2::4::3::5::8::6::0::9::7::1::nil) as L. exists L. pose (aux3_reflect 10 L).
  inversion r. auto.
Defined.
Definition ex_177_result_naive := permutation_power ex_177_permutation 150.
Eval compute in show ex_177_permutation.
Eval compute in show ex_177_result_naive.

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
