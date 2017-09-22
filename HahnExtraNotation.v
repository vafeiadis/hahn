(** Extra notations moved to separate file to avoid clashes. *)

Require Import HahnBase.

Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x != y" := (negb (x == y))
  (at level 70, no associativity) : bool_scope.
Notation "x != y :> T" := (negb (x == y :> T))
  (at level 70, y at next level) : bool_scope.
