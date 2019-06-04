From SharedTemperature Require Import TemperatureRange.
From SharedTemperature Require Import SharedRange.
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.

(* ------------------------------------------- *)

Definition shared_temperature T X Y : Z :=
  range_avg (shared_range T X Y).

Theorem st_comm :
  forall T X Y, shared_temperature T X Y = shared_temperature T Y X.
Proof. intros T X Y.
  unfold shared_temperature.
  rewrite sr_comm.
  reflexivity.
Qed.

(* TODO: st_as_good_as_any_alternative_in_total *)

(* TODO: st_no_advantage_to_lying *)

(* ------------------------------------------- *)
