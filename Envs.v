Require Import Compare_dec.
Require Import EqNat.
Require Import List.
Require Import Zdiv.

Require Import Types.

Set Implicit Arguments.

(**
  The operational semantics for this C fragment relies on an environment [Env],
  that has four components:
  - a map, [Mem], from addresses to values (modeling memory),
  - a map, [GlobalVar], from variable names to their addresses and atomic types
    (modeling global variables),
  - a map, [AllocMemBlock], from addresses of allocated memory blocks to their
    sizes (modeling runtime memory blocks allocated in heap), and
  - a stack, [StackVar] with the [top] of the stack, which models function
    frames, where each [Frame] maps variable names to their addresses and
    atomic types.

  [minAddress] and [maxAddress] bound the range of legal memory addresses
  where program data can reside. [minAddress] and [baseAddress] bound the range
  of global variables. Heap starts from [baseAddress], and stack starts from
  [maxAddress] in the reverse direction (note that [maxAddress] is never used).

  A memory [Mem] is defined only for addresses that have been allocated to
  the program by the C runtime.
  Our formalism axiomatizes #<a href="Top.Axioms.html">#properties#</a># of six
  primitive operations for accessing memory: read [accessMem], write [storeMem],
  malloc [umalloc], free [ufree], function frame allocation [ucreateFrame], and
  function frame deallocation [udestroyFrame].

  To model the instrumentation behavior, we extend the memory model with two
  additional components:
  - A map, [PmdTable], from addresses [Loc] to pointer metadata [Pmd]
    (modeling pointer metadata storage),
  - a map, [SndTable], from addresses [SndAddr] to status nodes [Snd]
    (modeling status node table).
  Each allocated location has associated metadata including a [Base], [Bound],
  and [SndAddr]. A status node with #<i>#invalid#</i># status indicates an
  unallocated address. The #<i>#global#</i># status is assigned to all global
  objects along with a unique global status node address [g_sa].
  Each [Frame] in a stack has its own status node address.

  Movec instruments the runtime primitives to support memory-safety metadata.
  read [accessMemPmd] and write [storeMemPmd] can access or store memory with
  associated metadata. During allocation, [malloc] or [createFrame] picks a
  free status node address for the new storage. Any pointer contained in this
  memory area is invalidated by invalidating its metadata. At deallocation,
  [free] or [destroyFrame] must assign invalid to the metadata of this storage.
  [free] also first ensures that the memory to deallocate is in heap by checking
  if the value stored in [SndTable] at its status node address is heap. *)

(******************************************************************************)
(** *                       Values                                            *)
(******************************************************************************)

(** [Value] is the contents stored in [Mem]. *)
Definition Value := nat.

(******************************************************************************)
(** *                       Locations                                         *)
(******************************************************************************)

(** [Loc] is the address of contents stored in [Mem]. *)
Definition Loc := Value.

(** Partitions of the address space.
  Function codes are allocated from [funAddress] to [minAddress];
  [GlobalVar] variables are allocted from [minAddress] to [baseAddress];
  Heap variables are allocted from [baseAddress] to the stack top;
  [StackVar] variables are allocated from the stack top to [maxAddress]. *)
Parameter funAddress : Loc.
Parameter minAddress : Loc.
Parameter baseAddress : Loc.
Parameter maxAddress : Loc.

(******************************************************************************)
(** *                       Metadata                                          *)
(******************************************************************************)

Definition Base := Loc.
Definition Bound := Loc.
Definition SndAddr := Loc. (* Status node address *)

(** Pointer metadata: *)
Definition Pmd := (Base * Bound * SndAddr)%type.

(** Storage of pointer metadata: *)
Definition PmdTable := Loc -> option Pmd.

(** Status of a referent: *)
Inductive Stat : Set :=
  | invalid : Stat
  | function : Stat
  | global : Stat
  | heap : Stat
  | stack : Stat.
(** Count of references to a referent: *)
Definition Count := nat.

(** Status node: *)
Definition Snd := (Stat * Count)%type.

(** Storage of status nodes of referents: *)
Definition SndTable := SndAddr -> option Snd.

(** Status node address for function memory: *)
Parameter f_sa : SndAddr.
(** Status node address for global memory: *)
Parameter g_sa : SndAddr.

(** Check for status equality. *)
Parameter eq_stat_dec :
  forall m n : Stat, { m = n } + { m <> n }.

(** Another Boolean version of eq_stat: NOT USED YET *)
Definition eq_stat_bool (m n : Stat) : bool :=
  match n with
  | invalid =>
    match m with
    | invalid => true
    | _ => false
    end
  | function =>
    match m with
    | function => true
    | _ => false
    end
  | global =>
    match m with
    | global => true
    | _ => false
    end
  | heap =>
    match m with
    | heap => true
    | _ => false
    end
  | stack =>
    match m with
    | stack => true
    | _ => false
    end
end.

(** Allocating a fresh status entry in [SndTable]: *)
Parameter getFreshSEntry: SndTable -> option SndAddr.

Definition lookUpSndTableStat (ST: SndTable) sa : Stat :=
  match ST sa with
  | Some (s, _) => s
  | None => invalid
  end.

Definition lookUpSndTableCount (ST: SndTable) sa : option Count :=
  match ST sa with
  | Some (_, c) => Some c
  | None => None
  end.

(******************************************************************************)
(** *                   Functions and variables                               *)
(******************************************************************************)

(** Named functions: *)
Definition Fun := c_ident.

(** Named variables: *)
Definition Var := c_ident.

(******************************************************************************)
(** *                       Memory                                            *)
(******************************************************************************)

(** [Mem] is defined as a total mapping, but the memory access primitives
    [accessMem] and [storeMem] are partial.
    A location that is not in the domain of these primitives is unallocated. *)
Definition Mem := Loc -> Value.

(******************************************************************************)
(** *                      Global variables                                   *)
(******************************************************************************)

(** Global variables are allocated from [minAddress] to [baseAddress].
    [GlobalVar] maps each variable to its location and its atomic type. *)
Record GlobalVar : Set := MkGlobalVar
  {  gdata : Var -> option (Loc * AType) }.

Definition lookUpGlobalVar (G: GlobalVar) (v: Var) : option (Loc * AType) :=
  G.(gdata) v.

(******************************************************************************)
(** *                     Heap variables                                      *)
(******************************************************************************)

(** Heap variables are allocated from [baseAddress] to the stack [top].
    We do not explictly define the heap. *)

(******************************************************************************)
(** *                 Allocated memory blocks                                 *)
(******************************************************************************)

(** [AllocMemBlock] stores the memory block allocated via #<i>#malloc#</i>#,
    which maps the return address of #<i>#malloc#</i># to the end address
    of this block. Only the pointers with addresses in the domain of
    [AllocMemBlock] can be deallocated via #<i>#free#</i>#. *)
Definition AllocMemBlock := Base -> option Bound.

Definition addAllocMemBlock (amb: AllocMemBlock) (b: Base) e : AllocMemBlock :=
  fun (b0: Base) =>
    match eq_nat_dec b0 b with
    | left _ (* b0 = b *) => Some e
    | right _ (* b0 <> b *) => amb b0
    end.

Definition removeAllocMemBlock (amb: AllocMemBlock) (b: Base) : AllocMemBlock :=
  fun (b0: Base) =>
    match eq_nat_dec b0 b with
    | left _ (* b0 = b *) => None
    | right _ (* b0 <> b *) => amb b0
    end.

(******************************************************************************)
(** *                    Stack variables                                      *)
(******************************************************************************)

(** Stack variables are allocated from the stack [top] to [maxAddress].
    [frame] is a simplified frame, which maps variables to only atomic
    types, used by the well-formed syntax. [uFrame] is a C frame,
    which maps each variable to its location and type, and defines the start
    address and the end address of frame. All the data in [uFrame] are from
    [ufrom] to [uto]. [Frame] is a Movec frame with the status node address
    of this frame which are changed by [createFrame] and [destroyFrame]. *)

(** Simplified frame: *)
Definition frame := Var -> option AType.

(** Uninstrumented C frame: *)
Record uFrame : Set := MkuFrame {
  ufdata : Var -> option (Loc * AType);
  ufrom : Loc;
  uto : Loc }.

Definition uFrame2frame (uF: uFrame) : frame :=
  fun v =>
    match uF.(ufdata) v with
    | Some (_, t) => Some t
    | None => None
    end.

Definition lookUpuFrame (uF: uFrame) (v: Var) : option (Loc * AType) :=
  uF.(ufdata) v.

(** Instrumented C frame: *)
Record Frame : Set := MkFrame {
  fdata : Var -> option (Loc * AType);
  from : Loc;
  to : Loc;
  s_sa : SndAddr }.

Definition Frame2uFrame (F: Frame) : uFrame :=
  MkuFrame F.(fdata) F.(from) F.(to).

Definition Frames2uFrames (Fs: list Frame) :=
  map Frame2uFrame Fs.

Definition Frame2frame (F: Frame) : frame :=
  fun v =>
    match F.(fdata) v with
    | Some (_, t) => Some t
    | None => None
    end.

Definition lookUpFrame (F: Frame) (v: Var) : option (Loc * AType) :=
  F.(fdata) v.

(** Look up the status of a Frame: *)
Definition lookUpFrameStat (F: Frame) (ST: SndTable) : Stat :=
  match ST F.(s_sa) with
  | Some (s, _) => s
  | None => invalid
  end.

(** Look up the count of references to a Frame: *)
Definition lookUpFrameCount (F: Frame) (ST: SndTable) : option Count :=
  match ST F.(s_sa) with
  | Some (_, c) => Some c
  | None => None
  end.

(** Uninstrumented C stack: *)
Record uStackVar : Set := MkuStackVar {
  uframes : list uFrame;
  utop : Loc (* top of the ustack *) }.

Definition uStackVar2frame (uS: uStackVar) : frame :=
  match head uS.(uframes) with
  | Some uF => uFrame2frame uF
  | None => fun v => None
  end.

Definition lookUpuStackVar (uS: uStackVar) (v: Var) : option (Loc * AType) :=
  match head uS.(uframes) with
  | Some uF =>
    match lookUpuFrame uF v with
    | Some (l, t) => Some (l, t)
    | None => None
    end
  | None => None
  end.

(** Instrumented C stack: *)
Record StackVar : Set := MkStackVar {
  frames : list Frame;
  top : Loc;     (* top of the stack *)
  l_sa : SndAddr (* status node address of the latest frame *) }.

Definition StackVar2uStackVar (S: StackVar) : uStackVar :=
  MkuStackVar (Frames2uFrames S.(frames)) S.(top).

Definition StackVar2frame (S: StackVar) : frame :=
  match head S.(frames) with
  | Some F => Frame2frame F
  | None => fun v => None
  end.

Definition lookUpStackVar (S: StackVar) (v: Var)
         : option (Loc * AType * SndAddr) :=
  match head S.(frames) with
  | Some F =>
    match lookUpFrame F v with
    | Some (l, t) => Some (l, t, F.(s_sa))
    | None => None
    end
  | None => None
  end.

(******************************************************************************)
(** *                       Environments                                      *)
(******************************************************************************)

Record uEnv : Set := MkuEnv {
  umem : Mem;
  uglobalvar : GlobalVar;
  uamb : AllocMemBlock;
  ustackvar : uStackVar }.

Record Env : Set := MkEnv {
  mem : Mem;
  globalvar : GlobalVar;
  amb : AllocMemBlock;
  stackvar : StackVar;
  pmdtable : PmdTable;
  sndtable : SndTable }.

Definition Env2uEnv (E: Env) : uEnv :=
  MkuEnv E.(mem) E.(globalvar) E.(amb) (StackVar2uStackVar E.(stackvar)).

(******************************************************************************)
(** *                      Primitives                                         *)
(******************************************************************************)

(** The axiomatization of the primitives below is defined in
    #<a href="Top.Axioms.html">#Axioms.v#</a>#. *)

(** Reading and writing memory locations: *)
Parameter accessMem : Mem -> Loc-> option Value.
Parameter storeMem : Mem -> Loc -> Value -> option Mem.

(** Memory allocation and deallocation: *)
Parameter umalloc : uEnv -> Value -> option (uEnv * Base).
Parameter ufree : uEnv -> Loc -> option uEnv.

(** Frames allocation and deallocation: *)
Parameter ucreateFrame : uEnv -> frame -> option uEnv.
Parameter udestroyFrame : uEnv -> option uEnv.

Definition validAddress (M: Mem) (l: Loc) :=
  exists v, accessMem M l = Some v.

(** Instrumented functions for Movec: *)

(** Predicates [check_dpv], [check_dpfv] and [check_free] check that the
    location is safe to access w.r.t. its metadata at pointer dereference,
    function pointer dereference and deallocation, respectively. *)

(** Check for memory errors when dereferencing a pointer variable who
    has the value v and the metadata pmd, and is of the pointer type a. *)
Definition check_dpv (ST: SndTable) (v: Value) (pmd: Pmd) (a: AType) : Prop :=
  match (v, pmd) with
  | (l, (b, e, sa)) =>
    match a with
    | A_Int => True
    | A_Pointer (R_AType a') => (* a = a'* *)
        b <> 0 /\ b <= l /\ l + sizeOfAType a' <= e /\
        sa <> 0 /\ lookUpSndTableStat ST sa <> invalid /\
        lookUpSndTableStat ST sa <> function
    | A_Pointer (R_Struct s) => (* a = s*  *)
        b <> 0 /\ b <= l /\ l + sizeOfStruct s <= e /\
        sa <> 0 /\ lookUpSndTableStat ST sa <> invalid /\
        lookUpSndTableStat ST sa <> function
    | A_Pointer (R_Name n) =>   (* a = n*  *)
      match typeTable n with
      | Some s =>
        b <> 0 /\ b <= l /\ l + sizeOfStruct s <= e /\
        sa <> 0 /\ lookUpSndTableStat ST sa <> invalid /\
        lookUpSndTableStat ST sa <> function
      | None => False
      end
    | A_Pointer R_Void => False
    | A_Pointer R_Func => False
    end
  end.

(** Check for memory errors when dereferencing a function pointer variable who
    has the value v and the metadata pmd. *)
Definition check_dpfv (ST: SndTable) (v: Value) (pmd: Pmd) : Prop :=
  match (v, pmd) with
  | (l, (b, e, sa)) =>
    b <> 0 /\ l = b /\
    sa <> 0 /\ lookUpSndTableStat ST sa <> invalid /\
    lookUpSndTableStat ST sa = function
  end.

(** Check for memory errors when deallocating a block via a pointer variable who
    has the value v and the metadata pmd. *)
Definition check_free (ST: SndTable) (v: Value) (pmd: Pmd) : Prop :=
  match (v, pmd) with
  | (l, (b, e, sa)) =>
    b <> 0 /\ l = b /\
    sa <> 0 /\ lookUpSndTableStat ST sa <> invalid /\
    lookUpSndTableStat ST sa = heap
  end.

(** Check for memory leaks. Return False if the check fails. *)
Definition check_ml (ST: SndTable) (sa: SndAddr) : Prop :=
  sa <> 0 -> ~ ( lookUpSndTableStat ST sa = heap /\
                 match lookUpSndTableCount ST sa with
                 | Some c => c <= 1
                 | None => False
                 end ).

Parameter check_ml_dec :
  forall ST sa, { check_ml ST sa } + { ~ check_ml ST sa }.

(** Another Boolean version of check_ml: NOT USED YET *)
Definition check_ml_bool (ST: SndTable) (sa: SndAddr) : bool :=
  if eq_nat_dec sa 0 then (* sa = 0 *)
    true
  else (* sa <> 0 *)
    match lookUpSndTableStat ST sa with
    | heap =>
      match lookUpSndTableCount ST sa with
      | Some c =>
        match le_lt_dec c 1 with
        | left _ (* c <= 1 *) => false
        | right _ (* c > 1 *) => true
        end
      | None => true
      end
    | _ => true
    end
  .

Definition addSnd (ST: SndTable) sa snd : SndTable :=
  fun (sa0: SndAddr) =>
    match eq_nat_dec sa0 sa with
    | left _ => snd
    | right _ => ST sa0
    end.

Definition removeSnd (ST: SndTable) sa : SndTable :=
  fun (sa0: SndAddr) =>
    match eq_nat_dec sa0 sa with
    | left _ => None
    | right _ => ST sa0
    end.

(** Update the status node at location sa to the status node snd. *)
Definition updateSnd (ST: SndTable) sa snd : SndTable :=
  fun (sa0: SndAddr) =>
    match eq_nat_dec sa0 sa with
    | left _ => snd
    | right _ => ST sa0
    end.

Definition updateSndStat (ST: SndTable) sa s : SndTable :=
  fun (sa0: SndAddr) =>
    match eq_nat_dec sa0 sa with
    | left _ =>
      match ST sa with
      | Some (_, c) => Some (s, c)
      | None => None
      end
    | right _ => ST sa0
    end.

Definition updateSndCount (ST: SndTable) sa c : SndTable :=
  fun (sa0: SndAddr) =>
    match eq_nat_dec sa0 sa with
    | left _ =>
      match ST sa with
      | Some (s, _) => Some (s, c)
      | None => None
      end
    | right _ => ST sa0
    end.

Definition updateSndDec (ST: SndTable) sa : SndTable :=
  fun (sa0: SndAddr) =>
    match eq_nat_dec sa0 sa with
    | left _ =>
      match ST sa with
      | Some (s, c) => Some (s, c-1)
      | None => None
      end
    | right _ => ST sa0
    end.

Definition updateSndInc (ST: SndTable) sa : SndTable :=
  fun (sa0: SndAddr) =>
    match eq_nat_dec sa0 sa with
    | left _ =>
      match ST sa with
      | Some (s, c) => Some (s, c+1)
      | None => None
      end
    | right _ => ST sa0
    end.

Definition updatePmd (PT: PmdTable) (l: Loc) (pmd: Pmd) : PmdTable :=
  fun (l0: Loc) =>
    match eq_nat_dec l0 l with
    | left _ (* l0 = l *) => Some pmd
    | right _ (* l0 <> l *) => PT l0
    end.

Definition updatePmds (PT: PmdTable) (from: Loc) (to: Loc) (pmd: Pmd)
         : PmdTable :=
  fun (l0: Loc) =>
    match le_lt_dec from l0 with
    | left _ (* from <= l0 *) =>
      match le_lt_dec to l0 with
      | left _ (* to <= l0 *) => PT l0
      | right _ (* to > l0 *) => (updatePmd PT l0 pmd) l0
      end
    | right _ (* from > l0 *) => PT l0
    end.

Definition updatePmdSnd (PT: PmdTable) (ST: SndTable) (l: Loc) (pmd: Pmd)
         : PmdTable * SndTable * Prop :=
  match pmd with
  | (_, _, sa) =>
    match PT l with
    | Some (_, _, sa_l) =>
      if eq_nat_dec sa sa_l then (* the status node is the same *)
        (updatePmd PT l pmd, ST, True)
      else (* update to a new status node *)
        let ml := if check_ml_dec ST sa_l then True else False in
        let ST' := updateSndDec ST sa_l in
        let ST'' := removeSnd ST sa_l in
        match lookUpSndTableCount ST sa_l with
        | Some c =>
          if eq_nat_dec c 1 then (* c <= 1, sa_l is removed *)
            (updatePmd PT l pmd, updateSndInc ST'' sa, ml)
          else (* c > 1, sa_l's count is decreased *)
            (updatePmd PT l pmd, updateSndInc ST' sa, ml)
        | None => (* ST sa_l is invalid *)
            (updatePmd PT l pmd, updateSndInc ST sa, ml)
        end
    | None =>
        (updatePmd PT l pmd, updateSndInc ST sa, True)
    end
  end.

(** Update metadata w.r.t. the source and target types. An integer can be cast
    to a pointer with the restriction that the base and end fields are set to
    the value of the integer and the value plus the size of the referent type,
    respectively. *)
Definition dataCast (vp: Value * Pmd) (from: AType) (to: AType)
         : Value * Pmd :=
  match (vp, from, to) with
  | ((v, (b, e, sa)), A_Int, A_Pointer r) => (* cast from int to r* *)
    match le_lt_dec v 0 with
    | left _ (* v <= 0 *) => (v, (0, 0, 0))
    | right _ (* v > 0 *) =>
      match sizeOfRType r with
      | Some size => (v, (v, v + size, g_sa))
      | _ => vp
      end
    end
  | _ => vp
  end.

(** Reading from a location returns a value and the associated pmd. *)
Definition accessMemPmd (M: Mem) (PT: PmdTable) l
         : option (Value * option Pmd) :=
  match accessMem M l with
  | Some v => Some (v, PT l)
  | None => None
  end.

(** Writing to a location returns a new Mem, a new PmdTable, a new SndTable,
    and whether a memory leak has occurred during the write. *)
Definition storeMemPmd (M: Mem) (PT: PmdTable) (ST: SndTable) l vp
         : option (Mem * PmdTable * SndTable * Prop) :=
  match vp with
  | (v, pmd) =>
    match storeMem M l v with
    | Some M' =>
      match updatePmdSnd PT ST l pmd with
      | (PT', ST', ml) => Some (M', PT', ST', ml)
      end
    | None => None
    end
  end.

Definition malloc (E: Env) n : option (Env * Base * SndAddr) :=
  match getFreshSEntry E.(sndtable) with
  | Some sa => (* get a new status node in the status table *)
    match umalloc (Env2uEnv E) n with (* use umalloc to construct malloc *)
    | Some (uE', b) =>
      Some (MkEnv uE'.(umem)
                  uE'.(uglobalvar)
                  uE'.(uamb)
                  E.(stackvar)
                  E.(pmdtable)
                  (addSnd E.(sndtable) sa (Some (heap, 0))),
            b,
            sa)
    | None => None
    end
  | None => None
  end.

Definition free (E: Env) l : option Env :=
  match accessMemPmd E.(mem) E.(pmdtable) l with
  (* l is the address of the pointer variable *)
  | Some (v, Some (b, e, sa)) => (* v is the value of the pointer variable *)
    if eq_nat_dec v b then
      (* v = b.
         ufree ensures that [v, e') is unallocated if AMB v = Some e'.
         free should ensure that [v, e') covers [b, e).
         free can check if v is in [b, e), but to check v = b is sufficient.
         We should be able to prove that these two ways are equivalent.
         Since the latter one is simpler, we only check if v = b. *)
      if eq_stat_dec (lookUpSndTableStat E.(sndtable) sa) heap then
        (* The status of the block to be freed is heap *)
        match ufree (Env2uEnv E) l with (* use ufree to construct free *)
        | Some uE' =>
          Some (MkEnv uE'.(umem)
                      uE'.(uglobalvar)
                      uE'.(uamb)
                      E.(stackvar)
                      (updatePmd E.(pmdtable) l (0, 0, sa))
                      (updateSndStat E.(sndtable) sa invalid))
        | None => None
        end
      else None
    else None
  | Some (_, None) => None
  | None => None
  end.

Definition createFrame (E: Env) fr : option Env :=
  match getFreshSEntry E.(sndtable) with
  | Some sa => (* get a new status node in the status table *)
    match ucreateFrame (Env2uEnv E) fr with
    | Some uE' =>
      match head uE'.(ustackvar).(uframes) with
      | Some uF =>
        Some (MkEnv
                uE'.(umem)
                uE'.(uglobalvar)
                uE'.(uamb)
                (MkStackVar ((MkFrame
                                uF.(ufdata)
                                uF.(ufrom)
                                uF.(uto)
                                sa)::E.(stackvar).(frames))
                            uE'.(ustackvar).(utop)
                            sa)
                E.(pmdtable)
                (addSnd E.(sndtable) sa (Some (stack, 1)))
             )
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Definition destroyFrame (E: Env) : option Env :=
  match head E.(stackvar).(frames) with
  | Some F1 => (* match the first frame *)
    if eq_stat_dec (lookUpFrameStat F1 E.(sndtable)) stack then
      match udestroyFrame (Env2uEnv E) with
      | Some uE' =>
        let Fs := tail E.(stackvar).(frames) in
        match head Fs with
        | Some F2 => (* match the second frame *)
          Some (MkEnv uE'.(umem)
                      uE'.(uglobalvar)
                      uE'.(uamb)
                      (MkStackVar Fs uE'.(ustackvar).(utop) F2.(s_sa))
                      E.(pmdtable)
                      (updateSndDec
                        (updateSndStat E.(sndtable) F1.(s_sa) invalid)
                        F1.(s_sa)) )
        | None => (* no more frames left, i.e., the result stack is empty *)
          Some (MkEnv uE'.(umem)
                      uE'.(uglobalvar)
                      uE'.(uamb)
                      (MkStackVar Fs uE'.(ustackvar).(utop) 0)
                      E.(pmdtable)
                      (updateSndDec
                        (updateSndStat E.(sndtable) F1.(s_sa) invalid)
                        F1.(s_sa)) )
        end
      | None => None
      end
    else None
  | None => None
  end.

(******************************************************************************)
(** *                        Well-formedness                                  *)
(******************************************************************************)
(**
  The safety result relies on showing that certain well-formedness invariants
  are maintained by the instrumented program.
  A well-formed environment |- [Env] consists of:
  - a well-formed global storage [GlobalVar], which ensures that global
    variables are allocated with well-formed type information,
  - well-formed allocated memory regions [AllocMemBlock], which must be
    disjoint to each other,
  - a well-formed stack storage [StackVar], which ensures that local
    variables of a function are allocated at a frame with well-formed
    type information, and later frames are of lower addresses than
    earlier frames, and
  - a well-formed pointer metadata table [PmdTable], which ensures that
    the metadata associated with each allocated location loc is well-formed.
    If this location loc is accessible, its value v with metadata (b, e, sa)
    satisfies the property:
<<
    (b = 0) \/ (sa = 0) \/
    (lookUpSndTableStat ST sa <> invalid ->
     forall l, b <= l < e -> validAddress [Mem] l)
>>
  - The range of functions is within b and e if and only if sa = [f_sa];
    the range of global variables is within b and e if and only if sa = [g_sa];
    the range of a frame on the stack is within b and e, if and only if
    sa is equal to the status node address of that frame, or
    lookUpSndTableStat ST sa = invalid.
  - The status node addresses of functions and global variables are unique.
  - An allocated memory region in AMB is with metadata (b, e, sa),
    then for any accessible value v' with metadata (b', e', sa')
    that is also within this range, they satisfy:
<<
    sa <> sa' -> lookUpSndTableStat ST sa  = invalid \/
                 lookUpSndTableStat ST sa' = invalid
>>
*)

Definition wfGlobalVar (M: Mem) (G: GlobalVar) : Prop :=
  forall v l t,
    lookUpGlobalVar G v = Some (l, t) ->
    (* any location is within [minAddress, baseAddress) *)
    (minAddress <= l /\ l + sizeOfAType t <= baseAddress) /\
    (* data in GlobalVar exists in Mem *)
    (validAddress M l) /\
    (* no variables are overlapped *)
    (forall v' l' t',
       lookUpGlobalVar G v' = Some (l', t') ->
       l' <> l ->
       (l' >= l + sizeOfAType t \/ l >= l' + sizeOfAType t') )
  .

Definition wfAllocMemBlock (M: Mem) (AMB: AllocMemBlock) (S: StackVar) : Prop :=
  forall b e,
    AMB b = Some e ->
    (* any location is within [baseAddress, stack top) *)
    (baseAddress <= b < e /\ e <= S.(top)) /\
    (* data in AllocMemBlock exists in Mem *)
    (forall l : Loc,
       b <= l < e -> validAddress M l) /\
    (* no blocks are overlapped *)
    (forall b' e',
       AMB b' = Some e' ->
       b' <> b ->
       ((b' < b /\ e' <= b) \/ (b < b' /\ e <= b')) )
  .

Definition wfuFrameNoOverlapped (uF: uFrame) : Prop :=
  forall v l t,
    lookUpuFrame uF v = Some (l, t) ->
    (* no variables are overlapped *)
    (forall v' l' t',
       lookUpuFrame uF v' = Some (l', t') ->
       l' <> l ->
       (l' >= l + sizeOfAType t \/ l >= l' + sizeOfAType t') )
  .

Definition wfFrameNoOverlapped (F: Frame) : Prop :=
  forall v l t,
    lookUpFrame F v = Some (l, t) ->
    (* no variables are overlapped *)
    (forall v' l' t',
       lookUpFrame F v' = Some (l', t') ->
       l' <> l ->
       (l' >= l + sizeOfAType t \/ l >= l' + sizeOfAType t') )
  .

Definition wfFrame (M: Mem) (F: Frame) (ST: SndTable) : Prop :=
  (forall v l t,
     lookUpFrame F v = Some (l, t) ->
     (* any location is within [from, to) *)
     (F.(from) <= l /\ l + sizeOfAType t <= F.(to)) /\
     (* data in Frame exists in Mem *)
     (validAddress M l) ) /\
  (wfFrameNoOverlapped F) /\
  (* frame status must be consistent with its status node *)
  lookUpSndTableStat ST F.(s_sa) = stack
  .

(* A list of frames are well-formed, if
   the latest frame has a lower address interval than the previous ones. *)
Inductive wfFrames : StackVar -> Prop :=
  | wfFrames_nil :
      wfFrames (MkStackVar nil maxAddress 0)
  | wfFrames_cons : forall F Fs l_sa,
      (* condition on tail *)
      wfFrames (MkStackVar Fs F.(to) l_sa) ->
      (* conditions on head *)
      baseAddress < F.(from) ->
      F.(from) < F.(to) <= maxAddress ->
      (* result on head::tail *)
      wfFrames (MkStackVar (F::Fs) F.(from) F.(s_sa))
  .

Definition wfStackVar (M: Mem) (S: StackVar) (ST: SndTable) : Prop :=
  wfFrames S /\
  (forall F, In F S.(frames) -> wfFrame M F ST) /\
  (forall F1 F2,
    In F1 S.(frames) /\ In F2 S.(frames) /\ F1.(s_sa) = F2.(s_sa) ->
    F1 = F2)
  .

(* A well-formed pmd refers to invalid or valid memory addresses. *)
Definition wfPmd (M: Mem) (pmd: Pmd) (ST: SndTable) : Prop :=
  match pmd with
  | (b, e, sa) =>
    (b = 0) \/ (sa = 0) \/
    (* any location is within [minAddress, maxAddress) *)
    (((sa <> f_sa /\ minAddress <= b < e /\ e <= maxAddress) \/
      (sa  = f_sa /\ funAddress <= b < e /\ e <= minAddress)) /\
     (lookUpSndTableStat ST sa <> invalid ->
      (* data in [b, e) exists in Mem *)
      forall l : Loc,
        b <= l < e -> validAddress M l))
  end.

(* All the pmds in the pmd table are well-formed. *)
Definition wfPmdTable (M: Mem) (PT: PmdTable) (ST: SndTable) : Prop :=
  forall l,
    match (PT l) with
    | Some pmd => wfPmd M pmd ST
    | _ => True
    end
  .

Definition wfSndTable (E: Env) : Prop :=
  (* Special status node addresses. *)
  lookUpSndTableStat E.(sndtable) f_sa = function /\
  lookUpSndTableStat E.(sndtable) g_sa = global /\
  (* For these special status nodes: *)
  forall sa,
    (sa = f_sa \/
     sa = g_sa \/
     exists F, In F E.(stackvar).(frames) /\ sa = F.(s_sa)) ->
    (* The initial count is 1. *)
    ((~exists l b e,
      E.(pmdtable) l = Some (b, e, sa)) ->
     exists c, lookUpSndTableCount E.(sndtable) sa = Some c /\ c = 1) /\
    (* The existence of references leads to count 2. *)
    (( exists l b e,
      E.(pmdtable) l = Some (b, e, sa)) ->
     exists c, lookUpSndTableCount E.(sndtable) sa = Some c /\ c > 1) /\
    (* The existence of two references leads to count 3. *)
    (( exists l b e l' b' e',
      l <> l' /\
      E.(pmdtable) l = Some (b, e, sa) /\
      E.(pmdtable) l' = Some (b', e', sa)) ->
     exists c, lookUpSndTableCount E.(sndtable) sa = Some c /\ c > 2)
  .

(* A pmd that refers to a function should have the function SndAddr. *)
Definition wfFunctionPtr b sa : Prop :=
  0 < b < minAddress -> sa <> 0 -> sa = f_sa.

Definition wfNonFunctionPtr e sa : Prop :=
  minAddress < e -> sa <> 0 -> sa <> f_sa.

(* A pmd that refers to a global variable should have the global SndAddr. *)
Definition wfGlobalPtr b sa : Prop :=
  minAddress <= b < baseAddress -> sa <> 0 -> sa = g_sa.

Definition wfNonGlobalPtr e sa : Prop :=
  baseAddress < e <= maxAddress -> sa <> 0 -> sa <> g_sa.

(* A pmd that refers to a stack variable should have the stack's SndAddr. *)
Definition wfStackPtr (S: StackVar) (ST: SndTable) b e sa : Prop :=
  baseAddress <= b < e ->
  sa <> 0 ->
  forall F,
    In F S.(frames) ->
    (b <= F.(from) < e \/ F.(from) <= b < F.(to)) ->
    sa <> F.(s_sa) -> lookUpSndTableStat ST sa = invalid
  .

Definition wfNonStackPtr (S: StackVar) (ST: SndTable) b sa : Prop :=
  baseAddress <= b < S.(top) ->
  sa <> 0 ->
  lookUpSndTableStat ST sa <> invalid ->
  forall F,
    In F S.(frames) ->
    sa <> F.(s_sa)
  .

Definition wfUniqSEntryF (ST: SndTable) sa : Prop :=
  sa <> 0 ->
  lookUpSndTableStat ST sa = function ->
  sa = f_sa
  .

Definition wfUniqSEntryG (ST: SndTable) sa : Prop :=
  sa <> 0 ->
  lookUpSndTableStat ST sa = global ->
  sa = g_sa
  .

(* If the pmds of two pointer variables are overlapped on some AMB,
   then they should point to the same referent,
   or at least one of them points to an invalid referent. *)
Definition wfOverlappedAMB (E: Env) b e sa : Prop :=
  forall l' b' e' sa' b0 e0,
    E.(pmdtable) l' = Some (b', e', sa') ->
    E.(amb) b0 = Some e0 ->
    ((b <= b0 /\ b0 < e) \/ (b0 <= b /\ b < e0)) ->
    ((b' <= b0 /\ b0 < e') \/ (b0 <= b' /\ b' < e0)) ->
    funAddress <= b < e -> funAddress <= b' < e' ->
    sa <> 0 -> sa' <> 0 ->
    let s  := lookUpSndTableStat E.(sndtable) sa  in
    let s' := lookUpSndTableStat E.(sndtable) sa' in
    sa <> sa' -> (s = invalid \/ s' = invalid)
  .

(* If the pmds of two pointer variables are overlapped,
   then they should point to the same referent,
   or at least one of them points to an invalid referent.
   Note that [wfOverlappedAMB] is sufficient to the proofs,
   while this [wfOverlapped] is only an additional predicate. *)
Definition wfOverlapped (E: Env) b e sa : Prop :=
  forall l' b' e' sa',
    E.(pmdtable) l' = Some (b', e', sa') ->
    ((b <= b' /\ b' < e) \/ (b' <= b /\ b < e')) ->
    funAddress <= b < e -> funAddress <= b' < e' ->
    sa <> 0 -> sa' <> 0 ->
    let s  := lookUpSndTableStat E.(sndtable) sa  in
    let s' := lookUpSndTableStat E.(sndtable) sa' in
    sa <> sa' -> (s = invalid \/ s' = invalid)
  .

Definition wfEnv (E: Env) : Prop :=
  wfGlobalVar E.(mem) E.(globalvar) /\
  wfAllocMemBlock E.(mem) E.(amb) E.(stackvar) /\
  wfStackVar E.(mem) E.(stackvar) E.(sndtable) /\
  wfPmdTable E.(mem) E.(pmdtable) E.(sndtable) /\
  wfSndTable E /\
  (* Metadata for functions must be (_, _, f_sa) *)
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfFunctionPtr b sa) /\
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfNonFunctionPtr e sa) /\
  (* Metadata for global variables must be (_, _, g_sa) *)
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfGlobalPtr b sa) /\
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfNonGlobalPtr e sa) /\
  (* Metadata for stack frames *)
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfStackPtr E.(stackvar) E.(sndtable) b e sa) /\
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfNonStackPtr E.(stackvar) E.(sndtable) b sa) /\
  (* Unique function status node *)
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfUniqSEntryF E.(sndtable) sa) /\
  (* Unique global status node *)
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfUniqSEntryG E.(sndtable) sa) /\
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfOverlappedAMB E b e sa) /\
  (forall l b e sa,
    E.(pmdtable) l = Some (b, e, sa) ->
    wfOverlapped E b e sa)
  .
