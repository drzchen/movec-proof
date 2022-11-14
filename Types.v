Require Import Compare_dec.
Require Import EqNat.
Require Import Lia.
Require Import List.
Require Import Zdiv.

(******************************************************************************)
(** *                 Syntax of C types                                       *)
(******************************************************************************)
(**
  The formal model is intended to represent programs #<i>#after#</i>#
  they have already been compiled to a fairly low level intermediate
  representation in which all code and data structures have been flattened
  and all operations are expressed in terms of atomic data types.

  Let [c_ident] range over C identifiers, e.g., variable and struct names.
  #<i>#Atomic types#</i># [AType] are integers or pointers to
  #<i>#referent types#</i># [RType], which include anonymous and named
  #<i>#structure types#</i># [Struct], #<i>#void#</i># and #<i>#function#</i>#
  in addition to atomic types. We define an anonymous structure type [Struct]
  as a list of identifiers with atomic types. We assume that we have a partial
  map [typeTable] from names to anonymous structure types that represents
  #<i>#typedef#</i># in the source code. *)

Definition c_ident := nat.

Inductive AType : Set :=
  | A_Int: AType
  | A_Pointer: RType -> AType
with Struct : Set :=
  | S_Nil : Struct
  | S_Cons : c_ident -> AType -> Struct -> Struct
with RType : Set :=
  | R_AType : AType -> RType
  | R_Struct : Struct -> RType
  | R_Name : c_ident -> RType
  | R_Void : RType
  | R_Func : RType.

Parameter typeTable : c_ident -> option Struct.

(* begin hide *)
Scheme AType_mut_ind := Induction for AType Sort Prop
with Struct_mut_ind := Induction for Struct Sort Prop
with RType_mut_ind := Induction for RType Sort Prop.

Definition mutual_AType_Struct_ind P P' P'' :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 =>
    conj (@AType_mut_ind P P' P'' h1 h2 h3 h4 h5 h6 h7 h8)
         (conj (@Struct_mut_ind P P' P'' h1 h2 h3 h4 h5 h6 h7 h8)
               (@RType_mut_ind P P' P'' h1 h2 h3 h4 h5 h6 h7 h8)).
(* end hide *)

(******************************************************************************)
(** *                 Primitives                                              *)
(******************************************************************************)

Definition isPtr (a : AType) : Prop :=
  match a with
  | A_Pointer _ => True
  | _ => False
  end.

(**
  Atomic types are always of size one, which is the minimial granularity in
  our memory system. The size of an anonymous structure type is the number of
  its fields. However, the size of a referent type is a partial function, which
  fails if [typeTable] doesn't know the name of a named structure. *)

Definition sizeOfAType (a : AType) : nat :=
  match a with
  | A_Int => 1
  | A_Pointer _ => 1
  end.

Fixpoint sizeOfStruct (s : Struct) : nat :=
  match s with
  | S_Nil => 0
  | S_Cons _ a s' => sizeOfStruct s' + sizeOfAType a
  end.

Definition sizeOfRType (r : RType) : option nat :=
  match r with
  | R_AType a => Some (sizeOfAType a)
  | R_Struct s => Some (sizeOfStruct s)
  | R_Name n =>
      match typeTable n with
      | Some s => Some (sizeOfStruct s)
      | None => None
      end
  | R_Void => Some 1
  | R_Func => Some 1
  end.

(**
  Given an identifier, we can get its offset and atomic type if it is
  a field of a structure. *)

Fixpoint getStructOffset (s : Struct) (id : c_ident) {struct s} : option nat :=
  match s with
  | S_Nil => None
  | S_Cons n a s' =>
    if beq_nat n id then
      Some 0
    else
      match getStructOffset s' id with
      | Some o => Some (o + sizeOfAType a)
      | None => None
      end
  end.

Fixpoint getStructType (s : Struct) (id : c_ident) {struct s} : option AType :=
  match s with
  | S_Nil => None
  | S_Cons n a s' =>
    if beq_nat n id then
      Some a
    else
      getStructType s' id
  end.

(******************************************************************************)
(** *                 Well-formedness                                         *)
(******************************************************************************)
(**
  The well-formedness |-a, |-s, and |-r for atomic types [wf_AType],
  anonymous structure types [wf_Struct], and referent types [wf_RType] are
  defined mutually. Most of the cases are straightward. At case [wf_R_Name],
  a named structure is well-formed if the name is stored in the table
  [typeTable] with a well-formed anonymous structure type. *)

Inductive wf_AType : AType -> Prop :=
  | wf_A_Int: wf_AType A_Int
  | wf_A_Pointer: forall r,
      wf_RType r -> wf_AType (A_Pointer r)
with wf_Struct : Struct -> Prop :=
  | wf_S_Nil : wf_Struct S_Nil
  | wf_S_Cons : forall n a s,
      wf_AType a -> wf_Struct s -> wf_Struct (S_Cons n a s)
with wf_RType : RType -> Prop :=
  | wf_R_AType : forall a,
      wf_AType a -> wf_RType (R_AType a)
  | wf_R_Struct: forall s,
      wf_Struct s -> wf_RType (R_Struct s)
  | wf_R_Name: forall n s,
      typeTable n = Some s -> wf_Struct s -> wf_RType (R_Name n)
  | wf_R_Void: wf_RType R_Void
  | wf_R_Func: wf_RType R_Func.

(* begin hide *)
Scheme wf_AType_mut_ind := Induction for wf_AType Sort Prop
with wf_Struct_mut_ind := Induction for wf_Struct Sort Prop
with wf_RType_mut_ind := Induction for wf_RType Sort Prop.

Definition mutual_wf_AType_Struct_RType_ind P P' P'' :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 =>
    conj (@wf_AType_mut_ind P P' P'' h1 h2 h3 h4 h5 h6 h7 h8)
         (conj (@wf_Struct_mut_ind P P' P'' h1 h2 h3 h4 h5 h6 h7 h8)
               (@wf_RType_mut_ind P P' P'' h1 h2 h3 h4 h5 h6 h7 h8)).
(* end hide *)

Global Hint Constructors
  AType Struct RType wf_AType wf_Struct : core.
Global Hint Resolve
  wf_R_AType wf_R_Struct wf_R_Name wf_R_Void wf_R_Func : core.
