Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.

Definition constrain a b x : Z := Z.max a (Z.min b x).

Example constrain_test_inside : constrain 2 5 3 = 3.
Proof. reflexivity. Qed.

Example constrain_test_below : constrain 2 5 1 = 2.
Proof. reflexivity. Qed.

Example constrain_test_above : constrain 2 5 6 = 5.
Proof. reflexivity. Qed.

Theorem constrain_max_min :
  forall a b x,
    (a <= b)
    ->
    constrain a b x = Z.max a (Z.min b x).
Proof. intros a b x aleb. reflexivity. Qed.

Theorem constrain_min_max :
  forall a b x,
    (a <= b)
    ->
    constrain a b x = Z.min b (Z.max a x).
Proof. intros a b x aleb.
  unfold constrain.
  rewrite Z.max_min_distr.
  rewrite (Z.max_r a b aleb).
  reflexivity.
Qed.

Theorem constrain_between :
  forall a b x,
    (a <= b)
    ->
    ((a <= constrain a b x) /\ (constrain a b x <= b)).
Proof. intros a b x aleb.
  split.
   - rewrite (constrain_max_min a b x aleb). apply Z.le_max_l.
   - rewrite (constrain_min_max a b x aleb). apply Z.le_min_l.
Qed.

Definition distance x y : nat := Z.abs_nat (x - y).

Definition avg x y : Z := (x + y) / 2.

(* ------------------------------------------- *)

Definition temperature := Z.

Inductive range : Set :=
  | integer_in : temperature -> temperature -> range.

Definition is_range R :=
  match R with
  | integer_in a b => (a <= b)
  end.

Definition singleton a : range := integer_in a a.

Theorem singleton_is_range : forall a, is_range (singleton a).
Proof. intros a. simpl. apply Z.le_refl. Qed.

Definition range_avg R : temperature :=
  match R with
  | integer_in a b => avg a b
  end.

Definition range_distance_from T R : nat :=
  match R with
  | integer_in a b =>
    let T2 := constrain a b T in
    distance T T2
  end.

Example radist_test_inside : range_distance_from 3 (integer_in 2 5) = Z.to_nat 0.
Proof. reflexivity. Qed.

Example radist_test_below : range_distance_from 3 (integer_in 10 20) = Z.to_nat 7.
Proof. reflexivity. Qed.

Example radist_test_above : range_distance_from 72 (integer_in 4 50) = Z.to_nat 22.
Proof. reflexivity. Qed.

(* ------------------------------------------- *)
