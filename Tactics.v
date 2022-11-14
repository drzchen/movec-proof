Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

(******************************************************************************)
(** * A library of additional tactics: delineating cases in proofs            *)
(******************************************************************************)

(* Implementation note: We want [string_scope] to be available for the [Case]
   tactics below, but we want "++" to denote list concatenation. *)
Open Scope string_scope.
Open Scope list_scope.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move x at top
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

(* begin show *)
Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.
Ltac SSSSSCase name := Case_aux subsubsubsubsubcase name.
Ltac SSSSSSCase name := Case_aux subsubsubsubsubsubcase name.
Ltac SSSSSSSCase name := Case_aux subsubsubsubsubsubsubcase name.
Ltac SSSSSSSSCase name := Case_aux subsubsubsubsubsubsubsubcase name.
(* end show *)
