Require Import Compare_dec.
Require Import EqNat.
Require Import List.

Require Import Types.
Require Import Envs.
Require Import Syntax.

Set Implicit Arguments.

(******************************************************************************)
(** *                 Result and error types                                  *)
(******************************************************************************)
(**
  We augment this operational semantics to keep track of metadata and potential
  memory errors. A [Result] can be [RLoc] which is an address with a status
  node address (the result of a left-hand-side), [RVal] which is a value with
  a pointer metadata (the result of a right-hand-side), [ROK] which is the
  result of a successful command, [RAbort] when memory-safety check fails, or
  [RSystemError] when #<i>#malloc#</i>#, #<i>#free#</i>#, frame allocation, or
  frame deallocation fails. *)

Inductive Result: Set :=
  | RLoc : (Loc*SndAddr) -> Result (* instrumented result of left-hand-sides *)
  | RVal : (Value*Pmd) -> Result   (* instrumented result of right-hand-sides *)
  | ROK : Result                   (* instrumented result of commands *)
  | RAbort : Result                (* memory-safety check fails *)
  | RSystemError : Result
  .

Definition Error (R: Result) := (R = RAbort) \/ (R = RSystemError).

(******************************************************************************)
(** *                 Semantics of instrumented C fragment                    *)
(******************************************************************************)
(**
  Space precludes showing the full set of evaluation rules (most of which are
  completely standard or obvious). Instead, we highlight a few cases that
  illustrate the salient features.

  For evaluating a left-hand-side, [S_GVar] and [S_SVar] are similar to their
  standard semantics, but additionally find the corresponding status node
  address for the left-hand-side variable.

  The rules [S_Deref] and [S_Deref_Abort] evaluate a pointer dereference when
  the memory-safety check succeeds and fails, respectively:
<<
     E |-L lhs => (loc_sa, a* )
     accessMemPmd(E.M, E.PT, loc) = loc'_(b', e', sa')
     check_dpv(E.ST, loc'_(b', e', sa'), a* )
    --------------------------------------------------- :: S_Deref
     E |-L *lhs => (loc'_sa', a)

     E |-L lhs => (loc_sa, a* )
     accessMemPmd(E.M, E.PT, loc) = loc'_(b', e', sa')
     ~ check_dpv(E.ST, loc'_(b', e', sa'), a* )
    --------------------------------------------------- :: S_Deref_Abort
     E |-L *lhs => (Abort, a)
>>
  Here, lhs is first evaluated to loc, which is the address of a pointer with
  type a*. If the address loc is allocated, the function
  [accessMemPmd](E.M, E.PT, loc) returns loc'_(b', e', sa'), the value of that
  pointer loc' and its metadata (b', e', sa'). Because pointers can be
  out-of-bounds due to pointer arithmetic, before doing the dereference,
  these rules check whether loc' is within the bounds, and yield the error Abort
  when the bounds check fails. The checking of temporal errors ensures the
  memory pointed by this pointer is not deallocated or reallocated. Note that
  it is a memory violation if [accessMemPmd](E.M, E.PT, loc) = None, in which
  case neither rule above applies. However, according to the type safety
  properties described #<a href="Top.BehavSim.html">#later#</a>#, [accessMemPmd] will
  not fail at runtime.

  The rules [S_StructPos] and [S_StructPos_Abort] evaluate an access through
  a struct field when the memory-safety check succeeds and fails, respectively:
<<
     E |-L lhs => (loc_sa, s* )
     accessMemPmd(E.M, E.PT, loc) = loc'_(b', e', sa')
     getStructOffSet(s, id) = offset
     getStructType(s, id) = a
     check_dpv(E.ST, (loc' + offset)_(b', e', sa'), a* )
    ---------------------------------------------------- :: S_StructPos
     E |-L lhs->id => ((loc' + offset)_sa', a)

     E |-L lhs => (loc_sa, s* )
     accessMemPmd(E.M, E.PT, loc) = loc'_(b', e', sa')
     getStructOffSet(s, id) = offset
     getStructType(s, id) = a
     ~ check_dpv(E.ST, (loc' + offset)_(b', e', sa'), a* )
    ------------------------------------------------------ :: S_StructPos_Abort
     E |-L lhs->id => (Abort, a')
>>
  Here, [getStructOffSet] returns a field offset, which is less than or equal to
  sizeof(s), along with the atomic type a of the field id in struct type s.

  The rules [S_NamePos] and [S_NamePos_Abort] are similar to the above two rules.
*)

Inductive s_lhs : Env -> c_lhs -> Result -> AType -> Prop :=
  | S_GVar : forall E (vid: Var) (loc: Loc) (a: AType),
      (StackVar2frame (stackvar E)) vid = None ->
      lookUpGlobalVar E.(globalvar) vid = Some (loc, a) ->
      wf_AType a ->
      s_lhs E (C_Var vid) (RLoc (loc, g_sa)) a
  | S_SVar : forall E (vid: Var) (loc: Loc) (sa: SndAddr) (a: AType),
      lookUpStackVar E.(stackvar) vid = Some (loc, a, sa) ->
      wf_AType a ->
      s_lhs E (C_Var vid) (RLoc (loc, sa)) a
  | S_Deref : forall E lhs loc' sa' a loc sa b' e',
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_AType a)) ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', Some (b', e', sa')) ->
      (* runtime violation check *)
      check_dpv E.(sndtable) loc' (b', e', sa') (A_Pointer (R_AType a)) ->
      s_lhs E (C_Deref lhs) (RLoc (loc', sa')) a
  | S_Deref_ErrorProp : forall E lhs R a' a,
      s_lhs E lhs R a -> Error R ->
      s_lhs E (C_Deref lhs) R a'
  | S_Deref_Abort : forall E lhs a loc sa loc' pmd',
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_AType a)) ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', Some pmd') ->
      (* runtime violation check *)
      ~ check_dpv E.(sndtable) loc' pmd' (A_Pointer (R_AType a)) ->
      s_lhs E (C_Deref lhs) RAbort a
  | S_Deref_Abort_None : forall E lhs a loc sa loc',
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_AType a)) ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', None) ->
      (* runtime violation check *)
      s_lhs E (C_Deref lhs) RAbort a
  | S_StructPos : forall E lhs id loc' offset sa' a loc sa s b' e',
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_Struct s)) ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', Some (b', e', sa')) ->
      getStructOffset s id = Some offset ->
      getStructType s id = Some a ->
      (* runtime violation check *)
      check_dpv E.(sndtable) (loc' + offset) (b', e', sa') (A_Pointer (R_AType a)) ->
      s_lhs E (C_StructPos lhs id) (RLoc (loc' + offset, sa')) a
  | S_StructPos_ErrorProp : forall E lhs id R a' a,
      s_lhs E lhs R a -> Error R ->
      s_lhs E (C_StructPos lhs id) R a'
  | S_StructPos_Abort : forall E lhs id a' loc sa s loc' b' e' sa' offset a,
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_Struct s)) ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', Some (b', e', sa')) ->
      getStructOffset s id = Some offset ->
      getStructType s id = Some a ->
      (* runtime violation check *)
      ~ check_dpv E.(sndtable) (loc' + offset) (b', e', sa') (A_Pointer (R_AType a)) ->
      s_lhs E (C_StructPos lhs id) RAbort a'
  | S_StructPos_Abort_None : forall E lhs id a' loc sa s loc',
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_Struct s)) ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', None) ->
      (* runtime violation check *)
      s_lhs E (C_StructPos lhs id) RAbort a'
  | S_NamePos : forall E lhs id loc' offset sa' a loc sa n s b' e',
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_Name n)) ->
      typeTable n = Some s ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', Some (b', e', sa')) ->
      getStructOffset s id = Some offset ->
      getStructType s id = Some a ->
      (* runtime violation check *)
      check_dpv E.(sndtable) (loc' + offset) (b', e', sa') (A_Pointer (R_AType a)) ->
      s_lhs E (C_NamePos lhs id) (RLoc (loc' + offset, sa')) a
  | S_NamePos_ErrorProp : forall E lhs id R a' a,
      s_lhs E lhs R a -> Error R ->
      s_lhs E (C_NamePos lhs id) R a'
  | S_NamePos_Abort : forall E lhs id a' loc sa n s loc' b' e' sa' offset a,
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_Name n)) ->
      typeTable n = Some s ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', Some (b', e', sa')) ->
      getStructOffset s id = Some offset ->
      getStructType s id = Some a ->
      (* runtime violation check *)
      ~ check_dpv E.(sndtable) (loc' + offset) (b', e', sa') (A_Pointer (R_AType a)) ->
      s_lhs E (C_NamePos lhs id) RAbort a'
  | S_NamePos_Abort_None : forall E lhs id a' loc sa n s loc',
      s_lhs E lhs (RLoc (loc, sa)) (A_Pointer (R_Name n)) ->
      typeTable n = Some s ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (loc', None) ->
      (* runtime violation check *)
      s_lhs E (C_NamePos lhs id) RAbort a'
  .

(**
  For evaluating a right-hand-side, [S_Const], [S_Size], [S_Fun], [S_Lhs],
  [S_Ref], [S_Add_Int_Int] and [S_Alloc] are similar to their standard semantics,
  but additionally create the corresponding pmd or read the corresponding pmd
  from the pointer metadata table for the right-hand-side expression.
  The other rules [S_Cast] and [S_Add_Ptr_Int] keep track of pointers' values
  and their metadata when evaluating type casts and pointer arithmetic.

  Type casts propagate the metadata unchanged, except in the case of casting an
  integer to a pointer, in which case the base and bound are set to the
  interger's value and the value plus the size of the referent type.
  Subsequent bounds checks on the resulting pointers will fail if they exceed
  the range, ensuring that pointers created from integers can only be
  dereferenced in the range. This rule follows the Movec implementation.
<<
     E |-R rhs => (d, a, E')
     |-a a'
     dataCast d a a' = d'
    -------------------------------- :: S_Cast
     E |-R (a') rhs => (d', a', E')
>>

  Pointer arithmetic propagate the metadata associated with the original pointer
  to the metadata of the resulting pointer. Note that pointers can be
  temporarily out-of-bounds or with an invalid status at runtime.
  The operational semantics will not yield an error in such cases until
  the program attempts a dereference through the illegal pointer.
<<
     E |-R rhs1 => (loc_pmd1, r*, E')
     |-a r*
     sizeOfRType(r) = size
     E' |-R rhs2 => (n2_pmd2, int, E'')
    ------------------------------------------------------ :: S_Add_Ptr_Int
     E |-R rhs1 + rhs2 => ((loc + n2*size)_pmd1, r*, E'')
>>
*)

Inductive s_rhs : Env -> c_rhs -> Result -> AType -> Env -> Prop :=
  | S_Const : forall E n,
      s_rhs E (C_Const n) (RVal (n, (0, 0, 0))) A_Int E
  | S_Size : forall E r size,
      wf_RType r ->
      sizeOfRType r = Some size ->
      s_rhs E (C_Size r) (RVal (size, (0, 0, 0))) A_Int E
  | S_Fun : forall E fid fr c,
      funTable (C_Fun fid) = Some (fr, c) ->
      s_rhs E (C_Fun fid) (RVal (fid, (fid, fid + 1, f_sa))) (A_Pointer R_Func) E
  | S_Lhs : forall E lhs val pmd a loc sa,
      s_lhs E lhs (RLoc (loc, sa)) a ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (val, Some pmd) ->
      s_rhs E (C_Lhs lhs) (RVal (val, pmd)) a E
  | S_Lhs_None : forall E lhs val a loc sa,
      s_lhs E lhs (RLoc (loc, sa)) a ->
      accessMemPmd E.(mem) E.(pmdtable) loc = Some (val, None) ->
      s_rhs E (C_Lhs lhs) (RVal (val, (0, 0, 0))) a E
  | S_Lhs_ErrorProp : forall E lhs R a' a,
      s_lhs E lhs R a -> Error R ->
      s_rhs E (C_Lhs lhs) R a' E
  | S_Ref : forall E a lhs loc sa,
      s_lhs E lhs (RLoc (loc, sa)) a ->
      wf_AType (A_Pointer (R_AType a)) ->
      s_rhs E (C_Ref a lhs) (RVal (loc, (loc, loc + sizeOfAType a, sa))) (A_Pointer (R_AType a)) E
  | S_Ref_ErrorProp : forall E a lhs R,
      s_lhs E lhs R a -> Error R ->
      s_rhs E (C_Ref a lhs) R (A_Pointer (R_AType a)) E
  | S_Cast : forall E a' rhs d' E' d a,
      s_rhs E rhs (RVal d) a E' ->
      wf_AType a' ->
      dataCast d a a' = d' ->
      s_rhs E (C_Cast a' rhs) (RVal d') a' E'
  | S_Cast_ErrorProp : forall E a' rhs R a'' E' a,
      s_rhs E rhs R a E' -> Error R ->
      s_rhs E (C_Cast a' rhs) R a'' E'
  | S_Add_Int_Int : forall E rhs1 rhs2 n1 n2 E'' pmd1 E' pmd2,
      s_rhs E rhs1 (RVal (n1, pmd1)) A_Int E' ->
      s_rhs E' rhs2 (RVal (n2, pmd2)) A_Int E'' ->
      s_rhs E (C_Add rhs1 rhs2) (RVal (n1 + n2, (0, 0, 0))) A_Int E''
  | S_Add_Int_Int_ErrorProp1 : forall E rhs1 rhs2 R a' E' a,
      s_rhs E rhs1 R a E' -> Error R ->
      s_rhs E (C_Add rhs1 rhs2) R a' E'
  | S_Add_Int_Int_ErrorProp2 : forall E rhs1 rhs2 R a' E'' d1 E' a,
      s_rhs E rhs1 (RVal d1) A_Int E' ->
      s_rhs E' rhs2 R a E'' -> Error R ->
      s_rhs E (C_Add rhs1 rhs2) R a' E''
  | S_Add_Ptr_Int : forall E rhs1 rhs2 loc n2 size pmd1 r E'' E' pmd2,
      s_rhs E rhs1 (RVal (loc, pmd1)) (A_Pointer r) E' ->
      wf_AType (A_Pointer r) ->
      sizeOfRType r = Some size ->
      s_rhs E' rhs2 (RVal (n2, pmd2)) A_Int E'' ->
      s_rhs E (C_Add rhs1 rhs2) (RVal (loc + n2*size, pmd1)) (A_Pointer r) E''
  | S_Add_Ptr_Int_ErrorProp1 : forall E rhs1 rhs2 R a' E' a,
      s_rhs E rhs1 R a E' -> Error R ->
      s_rhs E (C_Add rhs1 rhs2) R a' E'
  | S_Add_Ptr_Int_ErrorProp2 : forall E rhs1 rhs2 R a' E'' d1 r E' a,
      s_rhs E rhs1 (RVal d1) (A_Pointer r) E' ->
      s_rhs E' rhs2 R a E'' -> Error R ->
      s_rhs E (C_Add rhs1 rhs2) R a' E''
  | S_Alloc : forall E r rhs loc n sa E'' pmd E' size,
      s_rhs E rhs (RVal (n, pmd)) A_Int E' ->
      wf_AType (A_Pointer r) ->
      sizeOfRType r = Some size ->
      size > 0 ->
      malloc E' n = Some (E'', loc, sa) -> (* outOfMem checking *)
      s_rhs E (C_Alloc r rhs) (RVal (loc, (loc, loc + n, sa))) (A_Pointer r) E''
  | S_Alloc_ErrorProp : forall E r rhs R a' E' a,
      s_rhs E rhs R a E' -> Error R ->
      wf_AType (A_Pointer r) ->
      s_rhs E (C_Alloc r rhs) R a' E'
  | S_Alloc_OutofMem : forall E r rhs a' E' n pmd size,
      s_rhs E rhs (RVal (n, pmd)) A_Int E' ->
      wf_AType (A_Pointer r) ->
      sizeOfRType r = Some size ->
      size > 0 ->
      malloc E' n = None -> (* outOfMem *)
      s_rhs E (C_Alloc r rhs) RSystemError a' E'
  .

(**
  For evaluating a command, [S_Skip] creates a successful result OK,
  while [S_Seq] propagates the successful results of sequential commands.
  Note that, once a memory-safety check fails or a SystemError occurs, the rules
  propagate memory errors to the top level, analogously to raising an exception.
  For example, [S_Seq_ErrorProp1] and [S_Seq_ErrorProp2] propagate the memory
  errors of sequential commands.
<<
     E  |-C c1 => (R, E')
     R is Abort or SystemError
    --------------------------- :: S_Seq_ErrorProp1
     E |-C c1 ; c2 => (R, E')

     E  |-C c1 => (OK, E')
     E' |-C c2 => (R, E'')
     R is Abort or SystemError
    --------------------------- :: S_Seq_ErrorProp2
     E |-C c1 ; c2 => (R, E'')
>>

  The rule [S_Assign_Ptr] evaluates a pointer assignment and propagates metadata
  from the right-hand-side to the left-hand-side. When a memory leak is detected,
  it returns the result Abort. The rule [S_Assign_NPtr] is similar to its
  standard semantics.

  A function call:
<<
     E |-R rhs => (loc_pmd, a, E')
     check_dpfv(E'.ST, loc_pmd)
     funTable(loc) = (fr, c)
     createFrame(E', fr) = E''
     E'' |-C c => (R, E''')
     ~ Error(R)
     destroyFrame(E''') = E4
    ------------------------------- :: S_Call
     E |-C rhs() => (R, E4)

     E |-R rhs => (loc_pmd, a, E')
     ~ check_dpfv(E'.ST, loc_pmd)
    ------------------------------- :: S_Call_Abort
     E |-C rhs() => (Abort, E')
>>

  #<i>#free#</i>#:
<<
     E |-R rhs => (loc_pmd, r*, E')
     check_free(E'.ST, loc_pmd) ->
     free(E', loc) = E''
    -------------------------------- :: S_Free
     E |-C free(rhs) => (OK, E'')

     E |-R rhs => (loc_pmd, r*, E')
     ~ check_free(E'.ST, loc_pmd)
    -------------------------------- :: S_Free_Abort
     E |-C free(rhs) => (Abort, E')
>>
*)

Inductive s_cmd : Env -> c_cmd -> Result -> Env -> Prop :=
  | S_Skip : forall E,
      s_cmd E (C_Skip) ROK E
  | S_Seq : forall E c1 c2 E'' E',
      s_cmd E c1 ROK E' ->
      s_cmd E' c2 ROK E'' ->
      s_cmd E (C_Seq c1 c2) ROK E''
  | S_Seq_ErrorProp1 : forall E c1 c2 R E',
      s_cmd E c1 R E' -> Error R ->
      s_cmd E (C_Seq c1 c2) R E'
  | S_Seq_ErrorProp2 : forall E c1 c2 R E'' E',
      s_cmd E c1 ROK E' ->
      s_cmd E' c2 R E'' -> Error R ->
      s_cmd E (C_Seq c1 c2) R E''
  | S_Assign_Ptr : forall E lhs rhs M'' G'' AMB'' K'' PT'' ST'' loc sa al d ar E' d' ml,
      s_lhs E lhs (RLoc (loc, sa)) al ->
      s_rhs E rhs (RVal d) ar E' ->
      isPtr al ->
      dataCast d ar al = d' ->
      storeMemPmd E'.(mem) E'.(pmdtable) E'.(sndtable) loc d' = Some (M'', PT'', ST'', ml) -> ml ->
      E'.(globalvar) = G'' ->
      E'.(amb) = AMB'' ->
      E'.(stackvar) = K'' ->
      s_cmd E (C_Assign lhs rhs) ROK (MkEnv M'' G'' AMB'' K'' PT'' ST'')
  | S_Assign_NPtr : forall E lhs rhs M'' G'' AMB'' K'' PT'' ST'' loc sa al d ar E' d',
      s_lhs E lhs (RLoc (loc, sa)) al ->
      s_rhs E rhs (RVal d) ar E' ->
      ~ isPtr al ->
      dataCast d ar al = d' ->
      storeMem E'.(mem) loc (fst d') = Some M'' ->
      E'.(globalvar) = G'' ->
      E'.(amb) = AMB'' ->
      E'.(stackvar) = K'' ->
      E'.(pmdtable) = PT'' ->
      E'.(sndtable) = ST'' ->
      s_cmd E (C_Assign lhs rhs) ROK (MkEnv M'' G'' AMB'' K'' PT'' ST'')
  | S_Assign_ErrorProp1 : forall E lhs rhs R al,
      s_lhs E lhs R al -> Error R ->
      s_cmd E (C_Assign lhs rhs) R E
  | S_Assign_ErrorProp2 : forall E lhs rhs R E' loc sa al ar,
      s_lhs E lhs (RLoc (loc, sa)) al ->
      s_rhs E rhs R ar E' -> Error R ->
      s_cmd E (C_Assign lhs rhs) R E'
  | S_Assign_Ptr_Abort : forall E lhs rhs E' loc sa al d ar d' M'' PT'' ST'' ml,
      s_lhs E lhs (RLoc (loc, sa)) al ->
      s_rhs E rhs (RVal d) ar E' ->
      isPtr al ->
      dataCast d ar al = d' ->
      storeMemPmd E'.(mem) E'.(pmdtable) E'.(sndtable) loc d' = Some (M'', PT'', ST'', ml) -> ~ ml ->
      s_cmd E (C_Assign lhs rhs) RAbort E'
  | S_Call : forall E rhs R E4 loc pmd a E' fr c E'' E''',
      s_rhs E rhs (RVal (loc, pmd)) a E' ->
      (* runtime violation check *)
      check_dpfv E'.(sndtable) loc pmd ->
      funTable (C_Fun loc) = Some (fr, c) ->
      createFrame E' fr = Some E'' ->
      s_cmd E'' c R E''' -> ~ Error R ->
      destroyFrame E''' = Some E4 ->
      s_cmd E (C_Call rhs) R E4
  | S_Call_ErrorProp1 : forall E rhs R E' a,
      s_rhs E rhs R a E' -> Error R ->
      s_cmd E (C_Call rhs) R E'
  | S_Call_ErrorProp2 : forall E rhs R E''' loc pmd a E' fr c E'',
      s_rhs E rhs (RVal (loc, pmd)) a E' ->
      (* runtime violation check *)
      check_dpfv E'.(sndtable) loc pmd ->
      funTable (C_Fun loc) = Some (fr, c) ->
      createFrame E' fr = Some E'' ->
      s_cmd E'' c R E''' -> Error R ->
      s_cmd E (C_Call rhs) R E'''
  | S_Call_Error1 : forall E rhs E' loc pmd a fr c,
      s_rhs E rhs (RVal (loc, pmd)) a E' ->
      (* runtime violation check *)
      check_dpfv E'.(sndtable) loc pmd ->
      funTable (C_Fun loc) = Some (fr, c) ->
      createFrame E' fr = None ->
      s_cmd E (C_Call rhs) RSystemError E'
  | S_Call_Error2 : forall E rhs E''' loc pmd a E' fr c E'' R,
      s_rhs E rhs (RVal (loc, pmd)) a E' ->
      (* runtime violation check *)
      check_dpfv E'.(sndtable) loc pmd ->
      funTable (C_Fun loc) = Some (fr, c) ->
      createFrame E' fr = Some E'' ->
      s_cmd E'' c R E''' -> ~ Error R ->
      destroyFrame E''' = None ->
      s_cmd E (C_Call rhs) RSystemError E'''
  | S_Call_Abort : forall E rhs E' loc pmd a,
      s_rhs E rhs (RVal (loc, pmd)) a E' ->
      (* runtime violation check *)
      ~ check_dpfv E'.(sndtable) loc pmd ->
      s_cmd E (C_Call rhs) RAbort E'
  | S_Free : forall E rhs E'' loc pmd r E',
      s_rhs E rhs (RVal (loc, pmd)) (A_Pointer r) E' ->
      (* runtime violation check *)
      check_free E'.(sndtable) loc pmd ->
      free E' loc = Some E'' ->
      s_cmd E (C_Free rhs) ROK E''
  | S_Free_ErrorProp : forall E rhs R E' a,
      s_rhs E rhs R a E' -> Error R ->
      s_cmd E (C_Free rhs) R E'
  | S_Free_Error : forall E rhs E' loc pmd r,
      s_rhs E rhs (RVal (loc, pmd)) (A_Pointer r) E' ->
      (* runtime violation check *)
      check_free E'.(sndtable) loc pmd ->
      free E' loc = None ->
      s_cmd E (C_Free rhs) RSystemError E'
  | S_Free_Abort : forall E rhs E' loc pmd r,
      s_rhs E rhs (RVal (loc, pmd)) (A_Pointer r) E' ->
      (* runtime violation check *)
      ~ check_free E'.(sndtable) loc pmd ->
      s_cmd E (C_Free rhs) RAbort E'
  .

(* begin hide *)
Tactic Notation "s_lhs_cases" tactic(first) tactic(c) :=
  first;
  [ c S_GVar | c S_SVar |
    c S_Deref | c S_Deref_ErrorProp |
    c S_Deref_Abort | c S_Deref_Abort_None |
    c S_StructPos | c S_StructPos_ErrorProp |
    c S_StructPos_Abort | c S_StructPos_Abort_None |
    c S_NamePos | c S_NamePos_ErrorProp |
    c S_NamePos_Abort | c S_NamePos_Abort_None ].

Tactic Notation "s_rhs_cases" tactic(first) tactic(c) :=
  first;
  [ c S_Const | c S_Size | c S_Fun |
    c S_Lhs | c S_Lhs_None | c S_Lhs_ErrorProp |
    c S_Ref | c S_Ref_ErrorProp |
    c S_Cast | c S_Cast_ErrorProp |
    c S_Add_Int_Int | c S_Add_Int_Int_ErrorProp1 |
                      c S_Add_Int_Int_ErrorProp2 |
    c S_Add_Ptr_Int | c S_Add_Ptr_Int_ErrorProp1 |
                      c S_Add_Ptr_Int_ErrorProp2 |
    c S_Alloc | c S_Alloc_ErrorProp | c S_Alloc_OutofMem ].

Tactic Notation "s_cmd_cases" tactic(first) tactic(c) :=
  first;
  [ c S_Skip |
    c S_Seq | c S_Seq_ErrorProp1 | c S_Seq_ErrorProp2 |
    c S_Assign_Ptr | c S_Assign_NPtr | c S_Assign_ErrorProp1 |
                     c S_Assign_ErrorProp2 | c S_Assign_Ptr_Abort |
    c S_Call | c S_Call_ErrorProp1 | c S_Call_ErrorProp2 |
               c S_Call_Error1 | c S_Call_Error2 | c S_Call_Abort |
    c S_Free | c S_Free_ErrorProp | c S_Free_Error | c S_Free_Abort ].
(* end hide *)

Global Hint Resolve S_GVar S_SVar S_Const S_Size S_Fun S_Lhs
  S_Ref S_Ref_ErrorProp S_Cast S_Add_Int_Int S_Skip : core.
