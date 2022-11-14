Require Import Compare_dec.
Require Import EqNat.
Require Import List.
Require Import Peano_dec.

Require Import Types.
Require Import Envs.
Require Import Syntax.

Set Implicit Arguments.

(**
  Given these operations, we define a straightforward operational semantics
  for this fragment of C that is undefined for programs that access deallocated
  memory locations. The standard operational semantics of C evaluates a
  left-hand-side of an assignment to an address. The value at that address is
  overwritten by the value that the corresponding right-hand-side evaluates to.
  Note that, because the compiler transformations that yield code in this
  intermediate form depend on source-program type information (to calculate
  struct field indices, for example) and Movec's instrumentation itself uses
  types, our non-standard semantics depends on source type information. *)

(******************************************************************************)
(** *                 Result and error types                                  *)
(******************************************************************************)

Inductive uResult: Set :=
  | uRLoc : Loc -> uResult   (* standard result of left-hand-sides *)
  | uRVal : Value -> uResult (* standard result of right-hand-sides *)
  | uROK : uResult           (* standard result of commands *)
  | uRSystemError : uResult
  .

Definition uError (R: uResult) := (R = uRSystemError).

(******************************************************************************)
(** *                 Semantics of C fragment                                 *)
(******************************************************************************)
(**
  These considerations lead to three large-step evaluation rules.
  Left-hand-sides evaluate to a result [uResult] R (which must be an address loc
  if successful) and its atomic type [AType] a. Such an evaluation has no
  effect on the environment, so we write the rule as: E |-L lhs => (R, a).
  Right-hand-sides also evaluate to a typed result R (which must be a value v
  if successful), but it may modify the environment E via memory allocation,
  causing it to E': E |-R rhs => E' |-R (R, a).
  Commands simply evaluate to a result, which must be [uROK] if successful, and
  assignments, function calls and free statements can update the environment E
  to a final environment E': E |-C c => E' |-C R.

  In the standard semantics, lhs is evaluated to a location of memory, and
  rhs is evaluated to a value stored in memory. For example,
<<
    int x, y;
    x = y;
>>
  The lhs x is evaluated to &x, while the rhs y is evaluated to y.
  The assignment does *(&x) = y, so that M(&x) = M(&y). Similarly, consider
<<
    int *x, *y;
    x = y;
>>
  The lhs x is evaluated to &x, while the rhs y is evaluated to y.
  This means x and y refer to the same location by this assignment. *)

(**
  [uEnv] |-L [c_lhs] => ([uResult], [AType]) defines the standard semantics of
  left-hand-side that evaluates each variable in a left-hand-side [c_lhs] to
  a result [uResult] and an atomic type [AType] assigned by environment [uEnv].

  A global variable:
<<
     E.fr(vid) = None
     E.G(vid) = (loc, a)
     |-a a
    ----------------------- :: uS_GVar
     E |-L vid => (loc, a)
>>
  A local variable:
<<
     E.fr(vid) = (loc, a)
     |-a a
    ----------------------- :: uS_SVar
     E |-L vid => (loc, a)
>>
  A pointer dereference:
<<
     E |-L lhs => (loc, a* )
     E.M(loc) = loc'
    ------------------------- :: uS_Deref
     E |-L *lhs => (loc', a)
>>
  A field of an anonymous struct:
<<
     E |-L lhs => (loc, s* )
     E.M(loc) = loc'
     getStructOffSet(s, id) = offset
     getStructType(s, id) = a
    ------------------------------------- :: uS_StructPos
     E |-L lhs->id => (loc' + offset, a)
>>
  A field of a named struct:
<<
     E |-L lhs => (loc, n* )
     typeTable(n) = s
     E.M(loc) = loc'
     getStructOffSet(s, id) = offset
     getStructType(s, id) = a
    ------------------------------------- :: uS_NamePos
     E |-L lhs->id => (loc' + offset, a)
>>
*)

Inductive us_lhs : uEnv -> c_lhs -> uResult -> AType -> Prop :=
  | uS_GVar : forall E (vid: Var) (loc: Loc) (a: AType),
      (uStackVar2frame (ustackvar E)) vid = None ->
      lookUpGlobalVar E.(uglobalvar) vid = Some (loc, a) ->
      wf_AType a ->
      us_lhs E (C_Var vid) (uRLoc loc) a
  | uS_SVar : forall E (vid: Var) (loc: Loc) (a: AType),
      lookUpuStackVar E.(ustackvar) vid = Some (loc, a) ->
      wf_AType a ->
      us_lhs E (C_Var vid) (uRLoc loc) a
  | uS_Deref : forall E lhs loc' a loc,
      us_lhs E lhs (uRLoc loc) (A_Pointer (R_AType a)) ->
      accessMem E.(umem) loc = Some loc' ->
      us_lhs E (C_Deref lhs) (uRLoc loc') a
  | uS_StructPos : forall E lhs id loc' offset a loc s,
      us_lhs E lhs (uRLoc loc) (A_Pointer (R_Struct s)) ->
      accessMem E.(umem) loc = Some loc' ->
      getStructOffset s id = Some offset ->
      getStructType s id = Some a ->
      us_lhs E (C_StructPos lhs id) (uRLoc (loc' + offset)) a
  | uS_NamePos : forall E lhs id loc' offset a loc n s,
      us_lhs E lhs (uRLoc loc) (A_Pointer (R_Name n)) ->
      typeTable n = Some s ->
      accessMem E.(umem) loc = Some loc' ->
      getStructOffset s id = Some offset ->
      getStructType s id = Some a ->
      us_lhs E (C_NamePos lhs id) (uRLoc (loc' + offset)) a
  .

(**
  [uEnv] |-R [c_rhs] => ([uResult], [AType], [uEnv]) defines the standard
  semantics of right-hand-side that evaluates each variable in a right-hand-side
  [c_rhs] to a result [uResult], an atomic type [AType] assigned by environment
  [uEnv], and a new environment [uEnv].

  An integer constant:
<<
    ------------------------ :: uS_Const
     E |-R n => (n, int, E)
>>
  The size of a well-formed referent type:
<<
     |-r r
     sizeOfRType(r) = size
    ----------------------------------- :: uS_Size
     E |-R sizeof(r) => (size, int, E)
>>
  A function name:
<<
     funTable(fid) = (fr, c)
    ------------------------------------- :: uS_Fun
     E |-R fid => (fid, void ( * )(), E)
>>
  A left-hand-side:
<<
     E |-L lhs => (loc, a)
     E.M(loc) = val
    -------------------------- :: uS_Lhs
     E |-R lhs => (val, a, E)
>>
  Here, we do not check whether val is a block including only the valid data,
  because reading invalid data does not hurt anything.

  An address of a left-hand-side:
<<
     E |-L lhs => (loc, a)
     |-a a*
    ---------------------------------- :: uS_Ref
     E |-R (a* ) &lhs => (loc, a*, E)
>>
  A cast:
<<
     E |-R rhs => (val, a, E')
     |-a a'
    --------------------------------- :: uS_Cast
     E |-R (a') rhs => (val, a', E')
>>
  By convertible, only the a's with the same type size can be convertable
  into each other. So val got from rhs can be safely reused by (a') rhs.

  We consider two kinds of additions: integer additions and pointer arithmetics.
<<
     E  |-R rhs1 => (n1, int, E')
     E' |-R rhs2 => (n2, int, E'')
    ------------------------------------------ :: uS_Add_Int_Int
     E |-R rhs1 + rhs2 => (n1 + n2, int, E'')

     E |-R rhs1 => (loc, r*, E')
     |-a r*
     sizeOfRType(r) = size
     E' |-R rhs2 => (n2, int, E'')
    ---------------------------------------------- :: uS_Add_Ptr_Int
     E |-R rhs1 + rhs2 => (loc + n2*size, r*, E'')
>>
  #<i>#malloc#</i>#:
<<
     E |-R rhs => (n, int, E')
     |-a r*
     sizeOfRtype(r) = size
     size > 0
     umalloc(E', n) = (E'', loc)
    ------------------------------------------- :: uS_Alloc
     E |-R (r* ) malloc(rhs) => (loc, r*, E'')
>>
*)

Inductive us_rhs : uEnv -> c_rhs -> uResult -> AType -> uEnv -> Prop :=
  | uS_Const : forall E n,
      us_rhs E (C_Const n) (uRVal n) A_Int E
  | uS_Size : forall E r size,
      wf_RType r ->
      sizeOfRType r = Some size ->
      us_rhs E (C_Size r) (uRVal size) A_Int E
  | uS_Fun : forall E fid fr c,
      funTable (C_Fun fid) = Some (fr, c) ->
      us_rhs E (C_Fun fid) (uRVal fid) (A_Pointer R_Func) E
  | uS_Lhs : forall E lhs val a loc,
      us_lhs E lhs (uRLoc loc) a ->
      accessMem E.(umem) loc = Some val ->
      us_rhs E (C_Lhs lhs) (uRVal val) a E
  | uS_Ref : forall E a lhs loc,
      us_lhs E lhs (uRLoc loc) a ->
      wf_AType (A_Pointer (R_AType a)) ->
      us_rhs E (C_Ref a lhs) (uRVal loc) (A_Pointer (R_AType a)) E
  | uS_Cast : forall E a' rhs val E' a,
      us_rhs E rhs (uRVal val) a E' ->
      wf_AType a' ->
      us_rhs E (C_Cast a' rhs) (uRVal val) a' E'
  | uS_Cast_ErrorProp : forall E a' rhs R a'' E' a,
      us_rhs E rhs R a E' -> uError R ->
      us_rhs E (C_Cast a' rhs) R a'' E'
  | uS_Add_Int_Int : forall E rhs1 rhs2 n1 n2 E'' E',
      us_rhs E rhs1 (uRVal n1) A_Int E' ->
      us_rhs E' rhs2 (uRVal n2) A_Int E'' ->
      us_rhs E (C_Add rhs1 rhs2) (uRVal (n1 + n2)) A_Int E''
  | uS_Add_Int_Int_ErrorProp1 : forall E rhs1 rhs2 R a' E' a,
      us_rhs E rhs1 R a E' -> uError R ->
      us_rhs E (C_Add rhs1 rhs2) R a' E'
  | uS_Add_Int_Int_ErrorProp2 : forall E rhs1 rhs2 R a' E'' n1 E' a,
      us_rhs E rhs1 (uRVal n1) A_Int E' ->
      us_rhs E' rhs2 R a E'' -> uError R ->
      us_rhs E (C_Add rhs1 rhs2) R a' E''
  | uS_Add_Ptr_Int : forall E rhs1 rhs2 loc n2 size r E'' E',
      us_rhs E rhs1 (uRVal loc) (A_Pointer r) E' ->
      wf_AType (A_Pointer r) ->
      sizeOfRType r = Some size ->
      us_rhs E' rhs2 (uRVal n2) A_Int E'' ->
      us_rhs E (C_Add rhs1 rhs2) (uRVal (loc + n2*size)) (A_Pointer r) E''
  | uS_Add_Ptr_Int_ErrorProp1 : forall E rhs1 rhs2 R a' E' a,
      us_rhs E rhs1 R a E' -> uError R ->
      us_rhs E (C_Add rhs1 rhs2) R a' E'
  | uS_Add_Ptr_Int_ErrorProp2 : forall E rhs1 rhs2 R a' E'' loc r E' a,
      us_rhs E rhs1 (uRVal loc) (A_Pointer r) E' ->
      us_rhs E' rhs2 R a E'' -> uError R ->
      us_rhs E (C_Add rhs1 rhs2) R a' E''
  | uS_Alloc : forall E r rhs loc E'' n E' size,
      us_rhs E rhs (uRVal n) A_Int E' ->
      wf_AType (A_Pointer r) ->
      sizeOfRType r = Some size ->
      size > 0 ->
      umalloc E' n = Some (E'', loc) ->
      us_rhs E (C_Alloc r rhs) (uRVal loc) (A_Pointer r) E''
  | uS_Alloc_ErrorProp : forall E r rhs R a' E' a,
      us_rhs E rhs R a E' -> uError R ->
      wf_AType (A_Pointer r) ->
      us_rhs E (C_Alloc r rhs) R a' E'
  | uS_Alloc_OutofMem : forall E r rhs a' E' n size,
      us_rhs E rhs (uRVal n) A_Int E' ->
      wf_AType (A_Pointer r) ->
      sizeOfRType r = Some size ->
      size > 0 ->
      umalloc E' n = None -> (* outOfMem *)
      us_rhs E (C_Alloc r rhs) uRSystemError a' E'
  .

(**
  [uEnv] |-C [c_cmd] => ([uResult], [uEnv]) defines the standard
  semantics of command that evaluates each command [c_cmd] to a result
  [uResult] and a new environment [uEnv].

  An empty command:
<<
    ----------------------- :: uS_Skip
     E |-C skip => (OK, E)
>>
  A sequence of commands:
<<
     E  |-C c1 => (OK, E')
     E' |-C c2 => (OK, E'')
    ---------------------------- :: uS_Seq
     E |-C c1 ; c2 => (OK, E'')
>>
  An assignment:
<<
     E |-L lhs => (loc, al)
     E |-R rhs => (val, ar, E')
     storeM E'.M loc val = M''
    ---------------------------------------------------- :: uS_Assign
     E |-C lhs = rhs => (OK, (M'', E'.G, E'.AMB, E'.S))
>>
  A function call:
<<
     E |-R rhs => (loc, a, E')
     funTable(loc) = (fr, c)
     ucreateFrame(E', fr) = E''
     E'' |-C c => (R, E''')
     ~ uError(R)
     udestroyFrame(E''') = E4
    -------------------------- :: uS_Call
     E |-C rhs() => (R, E4)
>>
  #<i>#free#</i>#:
<<
     E |-R rhs => (loc, r*, E')
     ufree(E', loc) = E''
    ------------------------------ :: uS_Free
     E |-C free(rhs) => (OK, E'')
>>
*)

Inductive us_cmd : uEnv -> c_cmd -> uResult -> uEnv -> Prop :=
  | uS_Skip : forall E,
      us_cmd E (C_Skip) uROK E
  | uS_Seq : forall E c1 c2 E'' E',
      us_cmd E c1 uROK E' ->
      us_cmd E' c2 uROK E'' ->
      us_cmd E (C_Seq c1 c2) uROK E''
  | uS_Seq_ErrorProp1 : forall E c1 c2 R E',
      us_cmd E c1 R E' -> uError R ->
      us_cmd E (C_Seq c1 c2) R E'
  | uS_Seq_ErrorProp2 : forall E c1 c2 R E'' E',
      us_cmd E c1 uROK E' ->
      us_cmd E' c2 R E'' -> uError R ->
      us_cmd E (C_Seq c1 c2) R E''
  | uS_Assign : forall E lhs rhs M'' G'' AMB'' K'' loc al val ar E',
      us_lhs E lhs (uRLoc loc) al ->
      us_rhs E rhs (uRVal val) ar E' ->
      storeMem E'.(umem) loc val = Some M'' ->
      E'.(uglobalvar) = G'' ->
      E'.(uamb) = AMB'' ->
      E'.(ustackvar) = K'' ->
      us_cmd E (C_Assign lhs rhs) uROK (MkuEnv M'' G'' AMB'' K'')
  | uS_Assign_ErrorProp1 : forall E lhs rhs R al,
      us_lhs E lhs R al -> uError R ->
      us_cmd E (C_Assign lhs rhs) R E
  | uS_Assign_ErrorProp2 : forall E lhs rhs R E' loc al ar,
      us_lhs E lhs (uRLoc loc) al ->
      us_rhs E rhs R ar E' -> uError R ->
      us_cmd E (C_Assign lhs rhs) R E'
  | uS_Call : forall E rhs R E4 loc a E' fr c E'' E''',
      us_rhs E rhs (uRVal loc) a E' ->
      funTable (C_Fun loc) = Some (fr, c) ->
      ucreateFrame E' fr = Some E'' ->
      us_cmd E'' c R E''' -> ~ uError R ->
      udestroyFrame E''' = Some E4 ->
      us_cmd E (C_Call rhs) R E4
  | uS_Call_ErrorProp1 : forall E rhs R E' a,
      us_rhs E rhs R a E' -> uError R ->
      us_cmd E (C_Call rhs) R E'
  | uS_Call_ErrorProp2 : forall E rhs R E''' loc a E' fr c E'',
      us_rhs E rhs (uRVal loc) a E' ->
      funTable (C_Fun loc) = Some (fr, c) ->
      ucreateFrame E' fr = Some E'' ->
      us_cmd E'' c R E''' -> uError R ->
      us_cmd E (C_Call rhs) R E'''
  | uS_Call_Error1 : forall E rhs E' loc a fr c,
      us_rhs E rhs (uRVal loc) a E' ->
      funTable (C_Fun loc) = Some (fr, c) ->
      ucreateFrame E' fr = None ->
      us_cmd E (C_Call rhs) uRSystemError E'
  | uS_Call_Error2 : forall E rhs E''' loc a E' fr c E'' R,
      us_rhs E rhs (uRVal loc) a E' ->
      funTable (C_Fun loc) = Some (fr, c) ->
      ucreateFrame E' fr = Some E'' ->
      us_cmd E'' c R E''' -> ~ uError R ->
      udestroyFrame E''' = None ->
      us_cmd E (C_Call rhs) uRSystemError E'''
  | uS_Free : forall E rhs E'' loc r E',
      us_rhs E rhs (uRVal loc) (A_Pointer r) E' ->
      ufree E' loc = Some E'' ->
      us_cmd E (C_Free rhs) uROK E''
  | uS_Free_ErrorProp : forall E rhs R E' a,
      us_rhs E rhs R a E' -> uError R ->
      us_cmd E (C_Free rhs) R E'
  | uS_Free_Error : forall E rhs E' loc r,
      us_rhs E rhs (uRVal loc) (A_Pointer r) E' ->
      ufree E' loc = None ->
      us_cmd E (C_Free rhs) uRSystemError E'
  .

(* begin hide *)
Tactic Notation "us_lhs_cases" tactic(first) tactic(c) :=
  first;
  [ c uS_GVar | c uS_SVar | c uS_Deref |
    c uS_StructPos | c uS_NamePos ].

Tactic Notation "us_rhs_cases" tactic(first) tactic(c) :=
  first;
  [ c uS_Const | c uS_Size | c uS_Fun | c uS_Lhs | c uS_Ref |
    c uS_Cast | c uS_Cast_ErrorProp |
    c uS_Add_Int_Int | c uS_Add_Int_Int_ErrorProp1 |
                       c uS_Add_Int_Int_ErrorProp2 |
    c uS_Add_Ptr_Int | c uS_Add_Ptr_Int_ErrorProp1 |
                       c uS_Add_Ptr_Int_ErrorProp2 |
    c uS_Alloc | c uS_Alloc_ErrorProp | c uS_Alloc_OutofMem ].

Tactic Notation "us_cmd_cases" tactic(first) tactic(c) :=
  first;
  [ c uS_Skip |
    c uS_Seq | c uS_Seq_ErrorProp1 | c uS_Seq_ErrorProp2 |
    c uS_Assign | c uS_Assign_ErrorProp1 | c uS_Assign_ErrorProp2 |
    c uS_Call | c uS_Call_ErrorProp1 | c uS_Call_ErrorProp2 |
                c uS_Call_Error1 | c uS_Call_Error2 |
    c uS_Free | c uS_Free_ErrorProp | c uS_Free_Error ].
(* end hide *)

Global Hint Resolve uS_GVar uS_SVar uS_Const uS_Size uS_Fun uS_Lhs uS_Ref
  uS_Cast uS_Add_Int_Int uS_Skip : core.
