Require Import Compare_dec.
Require Import Lia.
Require Import List.

Require Import Types.
Require Import Envs.

(******************************************************************************)
(** *                      Axioms for primitives                              *)
(**   (accessMem, storeMem, umalloc, ufree, ucreateFrame, udestroyFrame)      *)
(******************************************************************************)
(**
  The memory [Mem] is defined only for addresses that have been allocated to
  the program by the C runtime. The C runtime provides primitive operations
  for accessing the memory: [accessMem], [storeMem], [umalloc], [ufree],
  function frame allocation [ucreateFrame] and function frame deallocation
  [udestroyFrame]. Rather than committing to a particular implementation of
  these primitives, our formalism axiomatizes properties that any reasonable
  implementation should satisfy. *)

Axiom validAddressRange :
  0 < funAddress /\ funAddress <= minAddress /\
  minAddress <= baseAddress <= maxAddress.

(** An allocated status node in the status node table must be previously
    available for allocation. *)
Axiom getFreshSEntry__inversion : forall ST sa,
  getFreshSEntry ST = Some sa ->
  ST sa = None /\ sa <> 0 /\ sa <> f_sa /\ sa <> g_sa.

(**
  The axioms of [accessMem] and [storeMem] state simple properties like:
  ``reading a location after storing to it returns the value that was stored'',
  ``storing to a location does not affect any other location'',
  ``storing a value to a location is valid iff
    storing another value to it is valid'',
  ``reading a location is valid iff storing to it is valid''.

  Note that [accessMem] and [storeMem] fail if they try to access unallocated
  memory. *)

Axiom storeMem__accessMem : forall M loc val M',
  (* If we store val at loc, *)
  storeMem M loc val = Some M' ->
  (* then we can read val from loc, while *)
  accessMem M' loc = Some val /\
  (* the values at other valid addresses are not affected, and *)
  (forall l v, l <> loc ->
    accessMem M l = Some v -> accessMem M' l = Some v) /\
  (* the invalid addresses are still invalid. *)
  (forall l,
    accessMem M l = None -> accessMem M' l = None)
  .

Axiom storeMem__uniqBehavior : forall M l v v',
  ((exists M', storeMem M l v  = Some M') ->
   (exists M', storeMem M l v' = Some M')) /\
  (storeMem M l v = None -> storeMem M l v' = None)
  .

Axiom validAccessMem__validStoreMem : forall M l v,
  (exists v', accessMem M l = Some v') <-> (exists M', storeMem M l v = Some M')
  .

(**
  The axioms of [umalloc] and [ufree] enforce properties like:
  ``malloc returns a pointer to a memory block that was previously unallocated,
  and stores this block at the [AllocMemBlock] table'',
  ``free only deallocates a memory block stored at the [AllocMemBlock] table,
  and removes this block from the [AllocMemBlock] table'', and
  ``malloc and free do not alter the contents of irrelevant locations.''

  Note that [umalloc] fails if there is not enough space, and
  [ufree] fails if it tries to deallocate a memory block that is not
  at the [AllocMemBlock] table. *)

Axiom umalloc__inversion : forall uE n uM' uG' uAMB' uS' b,
  umalloc uE n = Some ((MkuEnv uM' uG' uAMB' uS'), b) ->
  exists uM uAMB,
  (* The global and stack variables are unchanged. *)
  uE = MkuEnv uM uG' uAMB uS' /\
  (* The allocated block is above the base address and below the stack. *)
  n > 0 /\ baseAddress <= b /\ b + n <= uE.(ustackvar).(utop) /\
  (* The values at valid addresses are not affected. *)
  (forall l v,
     accessMem uM l = Some v -> accessMem uM' l = Some v) /\
  (* The invalid addresses beyond the allocated block are still invalid. *)
  (forall l, l < b \/ l >= b + n ->
     accessMem uM l = None -> accessMem uM' l = None) /\
  (* The addresses inside the allocated block were previously invalid. *)
  (forall l, b <= l < b + n ->
     accessMem uM  l = None) /\
  (* The addresses inside the allocated block are valid and filled with 0. *)
  (forall l, b <= l < b + n ->
     accessMem uM' l = Some 0) /\
  (* The allocated block is added into the block table. *)
  uAMB' = addAllocMemBlock uAMB b (b + n)
  .

Axiom ufree__inversion : forall uE loc uM' uG' uAMB' uS',
  ufree uE loc = Some (MkuEnv uM' uG' uAMB' uS') ->
  exists uM uAMB b e,
  (* The global and stack variables are unchanged. *)
  uE = MkuEnv uM uG' uAMB uS' /\
  (* The deallocated block is [b, e). *)
  accessMem uM loc = Some b /\ uAMB b = Some e /\
  (* The addresses beyond the deallocated block are not affected. *)
  (forall l, l < b \/ l >= e ->
     accessMem uM l = accessMem uM' l) /\
  (* The addresses inside the deallocated block were previously valid. *)
  (forall l, b <= l < e ->
     exists v, accessMem uM l = Some v) /\
  (* The addresses inside the deallocated block are invalid. *)
  (forall l, b <= l < e ->
     accessMem uM' l = None) /\
  (* The deallocated block is above the base address and below the stack. *)
  baseAddress <= b /\ e <= uE.(ustackvar).(utop) /\
  (* The deallocated block is removed from the block table. *)
  uAMB' = removeAllocMemBlock uAMB b
  .

(**
  The axioms of [ucreateFrame] and [udestroyFrame] enforce properties like:
  ``creating a frame allocates a new frame on the top of the stack'',
  ``destroying a frame simply removes the latest frame from the stack'', and
  ``creating and destroying a frame do not alter the contents of irrelevant
  locations.''

  Note that [ucreateFrame] fails if there is not enough space, and
  [udestroyFrame] fails if it tries to destroy a frame from an empty stack. *)

Axiom ucreateFrame__inversion : forall uE fr uE',
  ucreateFrame uE fr = Some uE' ->
  exists uF',
  (* The global variables and allocated blocks are unchanged. *)
  uE.(uglobalvar) = uE'.(uglobalvar) /\
  uE.(uamb) = uE'.(uamb) /\
  (* The created frame uF' is instantiated from fr,
     is above the base address and strictly below the original stack. *)
  head uE'.(ustackvar).(uframes) = Some uF' /\
  uFrame2frame uF' = fr /\
  uStackVar2frame uE'.(ustackvar) = fr /\
  (forall v t, fr v = Some t ->
     exists l, lookUpuStackVar uE'.(ustackvar) v = Some (l, t) /\
               uF'.(ufrom) <= l < uF'.(uto)) /\
  uF'.(ufrom) = uE'.(ustackvar).(utop) /\
  uF'.(uto) = uE.(ustackvar).(utop) /\
  tail uE'.(ustackvar).(uframes) = uE.(ustackvar).(uframes) /\
  baseAddress < uE'.(ustackvar).(utop) < uE.(ustackvar).(utop) /\
  (* The values at valid addresses are not affected. *)
  (forall l v,
     accessMem uE.(umem) l = Some v -> accessMem uE'.(umem) l = Some v) /\
  (* The invalid addresses beyond the created frame are still invalid. *)
  (forall l, l < uF'.(ufrom) \/ l >= uF'.(uto) ->
     accessMem uE.(umem) l = None -> accessMem uE'.(umem) l = None) /\
  (* The addresses inside the created frame were previously invalid. *)
  (forall l, uF'.(ufrom) <= l < uF'.(uto) ->
     accessMem uE.(umem) l = None) /\
  (* The addresses inside the created frame are valid and filled with 0. *)
  (forall l, uF'.(ufrom) <= l < uF'.(uto) ->
     accessMem uE'.(umem) l = Some 0) /\
  (* The created frame is well-formed. *)
  wfuFrameNoOverlapped uF'
  .

Axiom udestroyFrame__inversion : forall uE uE',
  udestroyFrame uE = Some uE' ->
  exists uF,
  (* The global variables and allocated blocks are unchanged. *)
  uE.(uglobalvar) = uE'.(uglobalvar) /\
  uE.(uamb) = uE'.(uamb) /\
  (* The destroyed frame uF is the head frame of the stack. *)
  head uE.(ustackvar).(uframes) = Some uF /\
  uF.(uto) = uE'.(ustackvar).(utop) /\
  tail uE.(ustackvar).(uframes) = uE'.(ustackvar).(uframes) /\
  (* The addresses beyond the destroyed frame are not affected. *)
  (forall l v, l < uF.(ufrom) \/ l >= uF.(uto) ->
     accessMem uE.(umem) l = v -> accessMem uE'.(umem) l = v) /\
  (* The addresses inside the destroyed frame were previously valid. *)
  (forall l, uF.(ufrom) <= l < uF.(uto) ->
     exists v, accessMem uE.(umem) l = Some v) /\
  (* The addresses inside the destroyed frame are invalid. *)
  (forall l, uF.(ufrom) <= l < uF.(uto) ->
     accessMem uE'.(umem) l = None)
  .
