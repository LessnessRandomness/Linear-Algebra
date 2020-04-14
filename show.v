Set Implicit Arguments.
Require Import Arith String Omega.
Require Import permutations.
Open Scope string.

Class Show A : Type :=
  {
  show : A -> string
  }.

(*** Show nat ***)

(* Taken from https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html*)
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.
Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".
Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.


(*** Show fin ***)

Instance showFin n: Show (fin n) :=
{
  show := fun f => show (proj1_sig f)
}.


(*** Show vector ***)

Definition string_of_vector_partial A `{Show A} n (v: vector A n) (i: fin n): string.
Proof.
  destruct i. induction x.
  + exact (show (v (exist _ 0 l))).
  + assert (x < n) by intuition. pose (IHx H0). refine (s ++ "," ++ show (v (exist _ (S x) l))).
Defined.
Definition string_of_vector A `{Show A} n (v: vector A (S n)): string.
Proof.
  exact ("[" ++ string_of_vector_partial v (exist _ n (le_n _)) ++ "]").
Defined.
Instance showVector A n `{Show A}: Show (vector A (S n)) :=
{
  show := @string_of_vector _ _ _
}.


(*** Show matrix ***)

Instance showMatrix A n m `{Show A}: Show (matrix A (S n) (S m)) :=
{
  show := fun M => string_of_vector (row M)
}.


(*** Show permutation ***)

Instance showPermutation n: Show (permutation (S n)) :=
{
  show := fun p => show (proj1_sig p)
}.


(*** Show pair ***)

Instance showPair A `{Show A}: Show (A * A)%type :=
{
  show := fun p => "(" ++ show (fst p) ++ "," ++ show (snd p) ++ ")"
}.


(*** Show list ***)

Definition string_of_list A `{Show A} (L: list A): string.
Proof.
  induction L.
  + exact "[]".
  + exact (show a ++ "::" ++ IHL).
Defined.

Instance showList A `{Show A}: Show (list A) :=
{
  show := @string_of_list _ _
}.


(*** Show permutation_list ***)

Instance showPermutationList n: Show (permutation_list n) :=
{
  show := fun p => show (proj1_sig p)
}.
