From SharedTemperature Require Import TemperatureRange.
Require Import Bool.
Require Import ZArith.
Open Scope Z_scope.

(* ------------------------------------------- *)

Definition shared_range T X Y : range :=
  match X, Y with
  | integer_in xa xb, integer_in ya yb =>
    let a := Z.max xa ya in
    let b := Z.min xb yb in
    (* if there is an overlap, use that.
       otherwise, extend them towards the normal *)
    if a <=? b
    then integer_in a b
    else singleton (constrain b a T)
  end.

Theorem sr_is_range :
  forall T X Y,
    is_range X -> is_range Y -> is_range (shared_range T X Y).
Proof. intros T X Y.
  destruct X as [xa xb].
  destruct Y as [ya yb].
  simpl.
  intros xaleb yaleb.
  case_eq (Z.max xa ya <=? Z.min xb yb).
   - rewrite Z.leb_le. intro aleb. apply aleb.
   - rewrite Z.leb_gt. intro blta. apply singleton_is_range.
Qed.

Theorem sr_comm : forall T X Y, shared_range T X Y = shared_range T Y X.
Proof. intros T X Y.
  destruct X as [xa xb].
  destruct Y as [ya yb].
  simpl.
  rewrite Z.max_comm. rewrite Z.min_comm.
  reflexivity.
Qed.

(* TODO: sr_assoc *)

(* ------------------------------------------- *)
