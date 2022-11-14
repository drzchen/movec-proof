Require Import Compare_dec.
Require Import EqNat.
Require Import Lia.
Require Import List.
Require Import ZArith.

Require Import Types.
Require Import Envs.
Require Import Axioms.
Require Import Tactics.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

(** This file proves that primitives have reasonable behaviors. *)

(******************************************************************************)
(** * Type sizes and offsets                                                  *)
(******************************************************************************)

Lemma sizeOfAType_one : forall a,
  sizeOfAType a = 1.
Proof.
  destruct a.
  simpl. auto.
  simpl. auto.
Qed.

Global Hint Resolve sizeOfAType_one : core.

Lemma sizeOfStruct_ge_zero : forall s,
  sizeOfStruct s >= 0.
Proof.
  intros.
  induction s.
  simpl. lia.
  simpl. lia.
Qed.

Lemma getStructOffset__getStructType_interval : forall s id offset a,
  getStructOffset s id = Some offset ->
  getStructType s id = Some a ->
  offset + sizeOfAType a <= sizeOfStruct s.
Proof.
  induction s.
  intros.
  simpl in H.
  inversion H.

  intros.
  simpl in *.
  destruct (beq_nat c id).
    inversion H. inversion H0. subst. clear H0 H.
    assert (J := sizeOfStruct_ge_zero s).
    lia.

    remember (getStructOffset s id) as n.
    destruct n.
      apply sym_eq in Heqn.
      apply IHs with (a := a0) in Heqn.
      inversion H. subst. clear H.
      lia. auto.
      inversion H.
Qed.

Global Hint Resolve getStructOffset__getStructType_interval : core.

Lemma getStructType__getStructOffset : forall s id a,
  getStructType s id = Some a ->
  exists offset, getStructOffset s id = Some offset.
Proof.
  induction s; intros; simpl in *.
  inversion H.
  destruct (beq_nat c id).
  exists 0. auto.
  apply IHs in H.
  destruct H as [offset H].
  rewrite H.
  exists (offset+sizeOfAType a). auto.
Qed.

(******************************************************************************)
(** * The unique behavior and validity of [accessMem] and [storeMem]          *)
(******************************************************************************)

Lemma invalidAccessMem__invalidStoreMem : forall M l v,
  accessMem M l = None <-> storeMem M l v = None.
Proof.
  intros M l v.
  remember (accessMem M l) as v0.
  destruct v0.
    assert (exists v, accessMem M l = Some v) as H. exists v0; auto.
    assert (J := validAccessMem__validStoreMem M l v).
    apply J in H. clear Heqv0. clear J.
    split.
      intro J. inversion J.
      intro J. destruct H as [M' H]. rewrite J in H. inversion H.

    remember (storeMem M l v) as M'.
    destruct M'.
      assert (exists M', storeMem M l v = Some M') as H. exists m; auto.
      assert (J := validAccessMem__validStoreMem M l v).
      apply J in H. clear HeqM'. clear J.
      destruct H as [v' H].
      rewrite H in Heqv0. inversion Heqv0.

      split. auto. auto.
Qed.

(******************************************************************************)
(** * The valid address of [accessMem] and [storeMem]                         *)
(******************************************************************************)

Lemma validAccessMem__validAddress : forall M l,
  (exists v, accessMem M l = Some v) ->
  validAddress M l.
Proof.
  intros M l J.
  unfold validAddress.
  auto.
Qed.

Lemma invalidAccessMem__invalidAddress : forall M l,
  accessMem M l = None ->
  ~validAddress M l.
Proof.
  intros M l J.
  unfold not in *.
  unfold validAddress.
  intro J1.
  destruct J1 as [v J1].
  symmetry in J. rewrite J1 in J.
  inversion J.
Qed.

Lemma validStoreMem__validAddress : forall M l v,
  (exists M', storeMem M l v = Some M') ->
  validAddress M l.
Proof.
  intros M l v H.
  unfold validAddress.
  apply (validAccessMem__validStoreMem M l v).
  auto.
Qed.

Lemma invalidStoreMem__invalidAddress : forall M l v,
  storeMem M l v = None ->
  ~validAddress M l.
Proof.
  intros M l v.
  intro J.
  apply (@invalidAccessMem__invalidStoreMem M l v) in J.
  apply (@invalidAccessMem__invalidAddress M l) in J.
  auto.
Qed.

Lemma validStoreMem__validAddresses : forall M l v M' loc,
  storeMem M l v = Some M' ->
  (validAddress M loc <-> validAddress M' loc).
Proof.
  intros.
  unfold validAddress.

  split.
  intro.
  apply storeMem__accessMem in H.
  destruct H as [H1 [H2 _]].
  destruct H0 as [v0 H0].
  destruct (Nat.eq_dec l loc).
    subst. exists v. auto.
    apply H2 in H0. exists v0. auto. auto.

  intro.
  apply storeMem__accessMem in H.
  destruct H as [_ [_ H]].
  remember (accessMem M loc) as G.
  destruct G.
    exists v0. auto.

    symmetry in HeqG.
    apply H in HeqG. clear H.
    destruct H0.
    rewrite H in HeqG.
    inversion HeqG.
Qed.

Lemma validStoreMem__invalidAddresses : forall M l v M' loc,
  storeMem M l v = Some M' ->
  (~validAddress M loc <-> ~validAddress M' loc).
Proof.
  intros M l v M' loc H.
  apply (@validStoreMem__validAddresses M l v M' loc) in H.
  destruct H as [H1 H2].
  split.
    intro. unfold not. intro. apply H2 in H0. contradiction H.
    intro. unfold not. intro. apply H1 in H0. contradiction H.
Qed.

(******************************************************************************)
(** * [updatePmdSnd]                                                          *)
(******************************************************************************)

Lemma updatePmdSnd__inversion_PT : forall PT ST l p PT' ST' ml,
  updatePmdSnd PT ST l p = (PT', ST', ml) ->
  PT' l = Some p.
Proof.
  intros PT ST l p PT' ST' ml.
  intro H.
  unfold updatePmdSnd in H.
  destruct p as [[b e] sa].
  destruct (PT l).
    (* PT l is valid *)
    destruct p as [[b_l e_l] sa_l].
    destruct Nat.eq_dec.
      (* sa = sa_l *)
      inversion H.
      unfold updatePmd.
      destruct (Nat.eq_dec l l).
        auto.
        contradict n. auto.

      (* sa <> sa_l *)
      destruct lookUpSndTableCount.
        destruct (Nat.eq_dec c 1).
          inversion H.
          unfold updatePmd.
          destruct (Nat.eq_dec l l).
            auto.
            contradict n0. auto.
          inversion H.
          unfold updatePmd.
          destruct (Nat.eq_dec l l).
            auto.
            contradict n1. auto.
        inversion H.
        unfold updatePmd.
        destruct (Nat.eq_dec l l).
          auto.
          contradict n0. auto.

    (* PT l is invalid *)
    inversion H.
    unfold updatePmd.
    destruct (Nat.eq_dec l l).
      auto.
      contradict n. auto.
Qed.

(******************************************************************************)
(** * [accessMemPmd]                                                          *)
(******************************************************************************)

Lemma accessMemPmd__accessMem_Some : forall M PT l v p,
  accessMemPmd M PT l = Some (v, p) ->
  accessMem M l = Some v.
Proof.
  intros M PT l v p J.
  unfold accessMemPmd in *.
  destruct (accessMem M l).
    inversion J. auto.
    inversion J.
Qed.

Lemma accessMem__accessMemPmd_Some : forall M PT l v,
  accessMem M l = Some v ->
  exists p, accessMemPmd M PT l = Some (v, p).
Proof.
  intros M PT l v J.
  unfold accessMemPmd.
  rewrite J.
  exists (PT l). auto.
Qed.

Lemma accessMemPmd__accessMem_None : forall M PT l,
  accessMemPmd M PT l = None ->
  accessMem M l = None.
Proof.
  intros M PT l J.
  unfold accessMemPmd in *.
  destruct (accessMem M l).
    inversion J.
    auto.
Qed.

Lemma accessMem__accessMemPmd_None : forall M PT l,
  accessMem M l = None ->
  accessMemPmd M PT l = None.
Proof.
  intros M PT l J.
  unfold accessMemPmd.
  rewrite J. auto.
Qed.

Lemma accessMemPmd__inversion_PT : forall M PT l v p,
  accessMemPmd M PT l = Some (v, Some p) ->
  PT l = Some p.
Proof.
  unfold accessMemPmd.
  intros M PT l v p H.
  destruct (accessMem M l).
    inversion H. auto.
    inversion H.
Qed.

Lemma accessMemPmd__inversion : forall M PT loc val pmd val' M',
  accessMemPmd M  PT loc = Some (val, pmd) ->
  storeMem M loc val' = Some M' ->
  accessMemPmd M' PT loc = Some (val', pmd) /\
  (forall l v, l <> loc ->
    accessMemPmd M PT l = Some v -> accessMemPmd M' PT l = Some v) /\
  (forall l,
    accessMemPmd M PT l = None -> accessMemPmd M' PT l = None)
  .
Proof.
  intros M PT loc val pmd val' M' H1 H2.
  apply storeMem__accessMem in H2.
  destruct H2 as [H2 [H3 H4]].
  unfold accessMemPmd.
  split.
    rewrite H2.
    unfold accessMemPmd in H1.
    destruct (accessMem M loc).
      inversion H1. subst. auto.
      inversion H1.

  split.
    intros l v J1 J2.
    remember (accessMem M l) as v0.
    destruct v0.
      inversion J2. subst. clear J2.
      symmetry in Heqv0.
      apply H3 in Heqv0.
        rewrite Heqv0. auto.
        auto.
    inversion J2.

  intros l J1.
  remember (accessMem M l) as v.
  destruct v.
    inversion J1.

    symmetry in Heqv.
    apply H4 in Heqv.
    rewrite Heqv. auto.
Qed.

Lemma accessMemPmd_unchanged_storeMemPmd : forall M PT loc vpmd M' PT' loc',
  (forall l vp, l <> loc' ->
     accessMemPmd M PT l = Some vp -> accessMemPmd M' PT' l = Some vp) ->
  (forall l,
     accessMemPmd M PT l = None -> accessMemPmd M' PT' l = None) ->
  loc <> loc' ->
  accessMemPmd M' PT' loc = vpmd -> accessMemPmd M PT loc = vpmd.
Proof.
  intros M PT loc vpmd M' PT' loc' H1 H2 H3 H4.
  remember (accessMemPmd M PT loc) as AccessMP.
  destruct AccessMP.
  symmetry in HeqAccessMP.
  apply H1 in HeqAccessMP.
  rewrite H4 in HeqAccessMP. auto. auto.

  symmetry in HeqAccessMP.
  apply H2 in HeqAccessMP.
  rewrite H4 in HeqAccessMP. auto.
Qed.

Lemma accessMemPmd_unchanged_malloc : forall M PT loc vpmd M' PT' b e,
  (forall l vp,
      accessMemPmd M PT l = Some vp -> accessMemPmd M' PT' l = Some vp) ->
  (forall l, l < b \/ l >= e ->
      accessMemPmd M PT l = None -> accessMemPmd M' PT' l = None) ->
  (loc < b \/ loc >= e) ->
  accessMemPmd M' PT' loc = vpmd -> accessMemPmd M PT loc = vpmd.
Proof.
  intros M PT loc vpmd M' PT' b e H1 H2 H3 H4.
  remember (accessMemPmd M PT loc) as AccessMP.
  destruct AccessMP.
  symmetry in HeqAccessMP.
  apply H1 in HeqAccessMP.
  rewrite H4 in HeqAccessMP. auto.

  symmetry in HeqAccessMP.
  apply H2 in HeqAccessMP.
  rewrite H4 in HeqAccessMP. auto. auto.
Qed.

Lemma accessMemPmd_unchanged_free : forall M PT loc vpmd M' PT' ploc b e,
  (forall l vp, l < b \/ l >= e -> l <> ploc ->
      accessMemPmd M PT l = vp -> accessMemPmd M' PT' l = vp) ->
  (loc < b \/ loc >= e) -> loc <> ploc ->
  accessMemPmd M' PT' loc = vpmd -> accessMemPmd M PT loc = vpmd.
Proof.
  intros M PT loc vpmd M' PT' ploc b e H1 H2 H3 H4.
  remember (accessMemPmd M PT loc) as G.
  destruct G.
    symmetry in HeqG.
    apply H1 in HeqG; auto.
    rewrite H4 in HeqG; auto.

    symmetry in HeqG.
    apply H1 in HeqG; auto.
    rewrite H4 in HeqG; auto.
Qed.

Lemma accessMemPmd_unchanged_destroyFrame : forall M PT loc vpmd M' PT' b e,
  (forall l vp, l < b \/ l >= e ->
      accessMemPmd M PT l = vp -> accessMemPmd M' PT' l = vp) ->
  (loc < b \/ loc >= e) ->
  accessMemPmd M' PT' loc = vpmd -> accessMemPmd M PT loc = vpmd.
Proof.
  intros M PT loc vpmd M' PT' b e H1 H2 H3.
  remember (accessMemPmd M PT loc) as G.
  destruct G.
    symmetry in HeqG.
    apply H1 in HeqG; auto.
    rewrite H3 in HeqG; auto.

    symmetry in HeqG.
    apply H1 in HeqG; auto.
    rewrite H3 in HeqG; auto.
Qed.

(******************************************************************************)
(** * [storeMemPmd]                                                           *)
(******************************************************************************)

Lemma storeMemPmd__storeMem_Some : forall M PT ST l v p M' PT' ST' ml,
  storeMemPmd M PT ST l (v, p) = Some (M', PT', ST', ml) ->
  storeMem M l v = Some M'.
Proof.
  intros M PT ST l v p M' PT' ST' ml.
  intro H.
  unfold storeMemPmd in H.
  destruct (storeMem M l v).
    destruct (updatePmdSnd PT ST l p) as [[PT'0 ST'0] ml0].
    inversion H. auto.
    inversion H.
Qed.

Lemma storeMem__storeMemPmd_Some : forall M PT ST l v p M',
  storeMem M l v = Some M' ->
  exists PT' ST' ml, storeMemPmd M PT ST l (v, p) = Some (M', PT', ST', ml).
Proof.
  intros M PT ST l v p M'.
  intro H.
  unfold storeMemPmd.
  rewrite H.
  destruct (updatePmdSnd PT ST l p) as [[PT'0 ST'0] ml0].
  exists PT'0, ST'0, ml0. auto.
Qed.

Lemma storeMemPmd__storeMem_None : forall M PT ST l v p,
  storeMemPmd M PT ST l (v, p) = None ->
  storeMem M l v = None.
Proof.
  intros M PT ST l v p J.
  unfold storeMemPmd in J.
  destruct (storeMem M l v).
    destruct updatePmdSnd.
    destruct p0.
    inversion J.
    auto.
Qed.

Lemma storeMem__storeMemPmd_None : forall M PT ST l v p,
  storeMem M l v = None ->
  storeMemPmd M PT ST l (v, p) = None.
Proof.
  intros M PT ST l v p J.
  unfold storeMemPmd.
  rewrite J.
  auto.
Qed.

Lemma storeMemPmd__inversion_PT : forall M PT ST l v p M' PT' ST' ml,
  storeMemPmd M PT ST l (v, p) = Some (M', PT', ST', ml) ->
  PT' l = Some p /\
  (forall loc, loc <> l ->
    PT loc = PT' loc).
Proof.
  intros M PT ST l v p M' PT' ST' ml.
  unfold storeMemPmd.
  split.
    (* The 1st conjunct *)
    destruct (storeMem M l v).
      apply (@updatePmdSnd__inversion_PT PT ST l p PT' ST' ml).
      destruct (updatePmdSnd PT ST l p) as [[PT'0 ST'0] ml0].
      inversion H. auto.
      inversion H.

    (* The 2nd conjunct *)
    destruct (storeMem M l v).
      unfold updatePmdSnd in H.
      destruct p as [[b e] sa].
      destruct (PT l). destruct p as [[b_l e_l] sa_l].
        destruct (Nat.eq_dec sa sa_l).
          inversion H.
          intros loc HH.
          unfold updatePmd.
          destruct (Nat.eq_dec loc l).
            contradict HH. auto.
            auto.

          destruct lookUpSndTableCount.
            destruct (Nat.eq_dec c 1).
              inversion H.
              intros loc HH.
              unfold updatePmd.
              destruct (Nat.eq_dec loc l).
                contradict HH. auto.
                auto.

              inversion H.
              intros loc HH.
              unfold updatePmd.
              destruct (Nat.eq_dec loc l).
                contradict HH. auto.
                auto.

            inversion H.
            intros loc HH.
            unfold updatePmd.
            destruct (Nat.eq_dec loc l).
              contradict HH. auto.
              auto.

        inversion H.
        intros loc HH.
        unfold updatePmd.
        destruct (Nat.eq_dec loc l).
          contradict HH. auto.
          auto.

      inversion H.
Qed.

Lemma storeMemPmd__inversion : forall M PT ST loc val pmd M' PT' ST' ml,
  storeMemPmd M PT ST loc (val, pmd) = Some (M', PT', ST', ml) ->
  accessMemPmd M' PT' loc = Some (val, Some pmd) /\
  (forall l vp, l <> loc ->
    accessMemPmd M PT l = Some vp -> accessMemPmd M' PT' l = Some vp) /\
  (forall l,
    accessMemPmd M PT l = None -> accessMemPmd M' PT' l = None)
  .
Proof.
  intros M PT ST loc val pmd M' PT' ST' ml H.
  assert (HH := H).
  apply (@storeMemPmd__inversion_PT M PT ST loc val pmd M' PT' ST' ml) in H.
  destruct H as [H1 H2].
  apply (@storeMemPmd__storeMem_Some M PT ST loc val pmd M' PT' ST' ml) in HH.
  apply (@storeMem__accessMem) in HH.
  destruct HH as [H3 [H4 H5]].
  unfold accessMemPmd.
  split.
    (* The 1st conjunct *)
    rewrite H3.
    rewrite H1. auto.

    split.
    (* The 2nd conjunct *)
    intros l vp J1 J2.
    remember (accessMem M l) as v.
    destruct v.
    symmetry in Heqv. apply H4 in Heqv.
    rewrite Heqv.
    assert (PT l = PT' l). apply H2. auto.
    rewrite H in J2. auto. auto.
    inversion J2.

    (* The 3rd conjunct *)
    intros l J1.
    remember (accessMem M l) as v.
    destruct v.
      inversion J1.

      symmetry in Heqv.
      apply H5 in Heqv.
      rewrite Heqv. auto.
Qed.

(******************************************************************************)
(** * The unique behavior and validity of [accessMemPmd] and [storeMemPmd]    *)
(******************************************************************************)

Lemma accessMemPmd__uniqBehavior : forall M PT l vp vp',
  (accessMemPmd M PT l = Some vp ->
   accessMemPmd M PT l = Some vp' ->
   vp = vp') /\
  (accessMemPmd M PT l = None ->
   accessMemPmd M PT l = None).
Proof.
  intros M PT l vp vp'.
  split.
    intros J1 J2.
    unfold accessMemPmd in *.
    destruct (accessMem M l).
      inversion J1. inversion J2. auto.
      inversion J1.

    intros J1. auto.
Qed.

Lemma storeMemPmd__uniqBehavior : forall M PT ST l vp vp',
  ((exists MPS, storeMemPmd M PT ST l vp  = Some MPS) ->
   (exists MPS, storeMemPmd M PT ST l vp' = Some MPS)) /\
  (storeMemPmd M PT ST l vp  = None ->
   storeMemPmd M PT ST l vp' = None).
Proof.
  intros M PT ST l vp vp'.
  split; intro J.
    (* The 1st conjunct *)
    unfold storeMemPmd in *.
    destruct vp as [v pmd].
    destruct vp' as [v' pmd'].
    remember (storeMem M l v) as M'.
    destruct M'; symmetry in HeqM'.
      assert (exists M', storeMem M l v = Some M') as J'. exists m. auto.
      destruct (@storeMem__uniqBehavior M l v v') as [J1 _].
      apply J1 in J'. clear HeqM' J1.
      destruct J' as [M' J'].
      rewrite J'. clear J'.
      destruct (updatePmdSnd PT ST l pmd') as [[PT'0 ST'0] ml']. eauto.

      destruct J as [MPS J]. inversion J.

    (* The 2nd conjunct *)
    unfold storeMemPmd in *.
    destruct vp as [v pmd].
    destruct vp' as [v' pmd'].
    remember (storeMem M l v) as M'.
    destruct M'; symmetry in HeqM'.
      destruct (updatePmdSnd PT ST l pmd) as [[PT0 ST0] ml]. inversion J.

      destruct (@storeMem__uniqBehavior M l v v') as [_ J1].
      apply J1 in HeqM'. clear J J1.
      rewrite HeqM'. auto.
Qed.

Lemma validAccessMemPmd__validStoreMemPmd : forall M PT ST l vp,
  (exists vp0, accessMemPmd M PT l = Some vp0) <->
  (exists MPS, storeMemPmd M PT ST l vp = Some MPS).
Proof.
  intros M PT ST l vp.

  split; intro J.
  destruct J as [vp0 J].
  unfold accessMemPmd in J.
  remember (accessMem M l) as v.
  destruct v.
    clear J.
    symmetry in Heqv.
    assert (exists v, accessMem M l = Some v) as J. exists v; auto. clear Heqv.
    destruct vp as [v1 p1].
    assert (J1 := @validAccessMem__validStoreMem M l v1).
    apply J1 in J. clear J1.
    destruct J as [M' J].
    unfold storeMemPmd.
    rewrite J. clear J.
    destruct updatePmdSnd.
    destruct p. eauto.

    inversion J.

  destruct J as [[[[M' PT'] ST'] ml] J].
  unfold storeMemPmd in J.
  destruct vp as [v p].
  remember (storeMem M l v) as M'0.
  destruct M'0.
    clear J.
    symmetry in HeqM'0.
    assert (exists M', storeMem M l v = Some M') as J. exists m; auto.
    assert (J1 := @validAccessMem__validStoreMem M l v).
    apply J1 in J. clear J1.
    destruct J as [v' J].
    unfold accessMemPmd.
    rewrite J.
    exists (v', PT l). auto.

    inversion J.
Qed.

Lemma validAccessMemPmd__validAccessMem : forall M PT l,
  (exists vp, accessMemPmd M PT l = Some vp) <->
  (exists v,  accessMem M l = Some v).
Proof.
  intros M PT l.
  unfold accessMemPmd.
  split.
    intro J.
    remember (accessMem M l) as v.
    destruct v.
      exists v. auto.
      destruct J as [vp J]. inversion J.

    intro J.
    destruct J as [v J].
    rewrite J.
    exists (v, PT l). auto.
Qed.

Lemma validStoreMemPmd__validStoreMem : forall M PT ST l vp1 v2,
  (exists MPS, storeMemPmd M PT ST l vp1 = Some MPS) <->
  (exists M',  storeMem M l v2 = Some M').
Proof.
  intros M PT ST l vp1 v2.
  unfold storeMemPmd.

  split.
  intro J.
  destruct J as [MPS J].
  destruct vp1 as [v1 p1].
  remember (storeMem M l v1) as M'.
  destruct M'.
    clear J.
    destruct (@storeMem__uniqBehavior M l v1 v2) as [J _].
    apply J. clear J.
    exists m. auto.

    inversion J.

  intro J.
  destruct vp1 as [v1 p1].
  destruct (@storeMem__uniqBehavior M l v2 v1) as [J1 _].
  apply J1 in J. clear J1.
  destruct J as [M' J].
  rewrite J. clear J.
  destruct updatePmdSnd. destruct p.
  eauto.
Qed.

Lemma validAccessMemPmd__validStoreMem : forall M PT l v,
  (exists vp, accessMemPmd M PT l = Some vp) <->
  (exists M', storeMem M l v = Some M').
Proof.
  intros M PT l v.
  split.
    intro J.
    apply (@validAccessMemPmd__validAccessMem M PT l) in J.
    apply (@validAccessMem__validStoreMem M l v) in J. auto.

    intro J.
    apply (@validAccessMem__validStoreMem M l v) in J.
    apply (@validAccessMemPmd__validAccessMem M PT l) in J. auto.
Qed.

Lemma validStoreMemPmd__validAccessMem : forall M PT ST l vp,
  (exists MPS, storeMemPmd M PT ST l vp = Some MPS) <->
  (exists v,   accessMem M l = Some v).
Proof.
  intros M PT ST l vp.

  split; intro J.
  destruct vp as [v p].
  apply (@validStoreMemPmd__validStoreMem M PT ST l (v, p) v) in J.
  apply (@validAccessMem__validStoreMem M l v) in J.
  auto.

  apply (@validAccessMemPmd__validAccessMem M PT l) in J.
  apply (@validAccessMemPmd__validStoreMemPmd M PT ST l vp) in J.
  destruct J.
  exists x. auto.
Qed.

Lemma invalidAccessMemPmd__invalidStoreMemPmd : forall M PT ST l vp,
  (accessMemPmd M PT l = None) <->
  (storeMemPmd M PT ST l vp = None).
Proof.
  intros M PT ST l vp.

  split; intro J.
  unfold accessMemPmd in J.
  remember (accessMem M l) as v.
  destruct v.
    inversion J.

    clear J. destruct vp as [v p].
    destruct (@invalidAccessMem__invalidStoreMem M l v) as [J _].
    symmetry in Heqv. apply J in Heqv. clear J.
    unfold storeMemPmd.
    rewrite Heqv. auto.

  unfold storeMemPmd in J.
  destruct vp as [v p].
  remember (storeMem M l v) as M'.
  destruct M'.
    destruct updatePmdSnd. destruct p0.
    inversion J.

    clear J.
    symmetry in HeqM'.
    apply (@invalidAccessMem__invalidStoreMem M l v) in HeqM'.
    unfold accessMemPmd.
    rewrite HeqM'. auto.
Qed.

(******************************************************************************)
(** * The valid address of [accessMemPmd] and [storeMemPmd]                   *)
(******************************************************************************)

Lemma validAccessMemPmd__validAddress : forall M PT l,
  (exists vp, accessMemPmd M PT l = Some vp) ->
  validAddress M l.
Proof.
  intros M PT l J.
  destruct J as [[v p] J].
  apply (@accessMemPmd__accessMem_Some M PT l v p) in J.
  assert (exists v, accessMem M l = Some v) as H. exists v. auto.
  apply (@validAccessMem__validAddress M l) in H. auto.
Qed.

Lemma invalidAccessMemPmd__invalidAddress : forall M PT l,
  accessMemPmd M PT l = None ->
  ~validAddress M l.
Proof.
  intros M PT l J.
  apply (@accessMemPmd__accessMem_None M PT l) in J.
  apply (@invalidAccessMem__invalidAddress M l) in J. auto.
Qed.

Lemma validStoreMemPmd__validAddress : forall M PT ST l vp,
  (exists M' PT' ST' ml, storeMemPmd M PT ST l vp = Some (M', PT', ST', ml)) ->
  validAddress M l.
Proof.
  intros M PT ST l vp J.
  destruct vp as [v p].
  destruct J as [M' [PT' [ST' [ml J]]]].
  apply (@storeMemPmd__storeMem_Some M PT ST l v p M' PT' ST' ml) in J.
  assert (exists M', storeMem M l v = Some M') as J1. exists M'. auto.
  apply (@validStoreMem__validAddress M l v) in J1.
  auto.
Qed.

Lemma invalidStoreMemPmd__invalidAddress : forall M PT ST l vp,
  storeMemPmd M PT ST l vp = None ->
  ~validAddress M l.
Proof.
  intros M PT ST l vp J1.
  destruct vp as [v p].
  apply (@storeMemPmd__storeMem_None M PT ST l v) in J1.
  apply (@invalidStoreMem__invalidAddress M l v) in J1. auto.
Qed.

Lemma validStoreMemPmd__validAddresses : forall M PT ST l vp M' PT' ST' ml loc,
  storeMemPmd M PT ST l vp = Some (M', PT', ST', ml) ->
  (validAddress M loc <-> validAddress M' loc).
Proof.
  intros M PT ST l vp M' PT' ST' ml loc J.
  destruct vp as [v p].
  apply (@storeMemPmd__storeMem_Some M PT ST l v p M' PT' ST' ml) in J.
  apply (@validStoreMem__validAddresses M l v M' loc) in J.
  auto.
Qed.

Lemma validStoreMemPmd__invalidAddress: forall M PT ST l vp M' PT' ST' ml loc,
  storeMemPmd M PT ST l vp = Some (M', PT', ST', ml) ->
  (~validAddress M loc <-> ~validAddress M' loc).
Proof.
  intros M PT ST l vp M' PT' ST' ml loc J.
  destruct vp as [v p].
  apply (@storeMemPmd__storeMem_Some M PT ST l v p M' PT' ST' ml) in J.
  apply (@validStoreMem__invalidAddresses M l v M' loc) in J. auto.
Qed.

(******************************************************************************)
(** * [malloc]                                                                *)
(******************************************************************************)

Lemma malloc__inversion : forall E n M' G' AMB' S' PT' ST' b sa,
  malloc E n = Some ((MkEnv M' G' AMB' S' PT' ST'), b, sa) ->
  exists M AMB ST,
  (* The global and stack variables are unchanged. *)
  E = MkEnv M G' AMB S' PT' ST /\
  (* The allocated block is above the base address and below the stack. *)
  n > 0 /\ baseAddress <= b /\ b + n <= E.(stackvar).(top) /\
  (* The values at valid addresses are not affected. *)
  (forall l vp,
     accessMemPmd M PT' l = Some vp -> accessMemPmd M' PT' l = Some vp) /\
  (* The invalid addresses beyond the allocated block are still invalid. *)
  (forall l, l < b \/ l >= b + n ->
     accessMemPmd M PT' l = None -> accessMemPmd M' PT' l = None) /\
  (* The addresses inside the allocated block were previously invalid. *)
  (forall l, b <= l < b + n ->
     accessMemPmd M PT' l = None) /\
  (* The addresses inside the allocated block are valid and filled with 0. *)
  (forall l, b <= l < b + n ->
     accessMemPmd M' PT' l = Some (0, PT' l)) /\
  (* The allocated block is added into the block table. *)
  AMB' = addAllocMemBlock AMB b (b + n) /\
  (*! The allocated status node indicates the heap storage. *)
  ST sa = None /\ sa <> 0 /\ sa <> f_sa /\ sa <> g_sa /\
  ST' sa = Some (heap, 0) /\
  (*! The other status nodes are not affected. *)
  (forall a, a <> sa ->
     ST a = ST' a)
  .
Proof.
  intros E n M' G' AMB' S' PT' ST' b sa H.
  unfold malloc in H.
  remember (umalloc (Env2uEnv E) n) as UMalloc.
  unfold Env2uEnv in HeqUMalloc.
  unfold StackVar2uStackVar in HeqUMalloc.
  destruct E as [M G AMB [frs top lsa] PT ST].
  simpl in *.
  remember (getFreshSEntry ST) as GetFreshSEntry.
  destruct GetFreshSEntry.
    symmetry in HeqGetFreshSEntry.
    destruct UMalloc. destruct p as [[uM' uG' uAMB' uS'] ub].
      (* Both getFreshSEntry and umalloc are valid *)
      symmetry in HeqUMalloc.
      apply umalloc__inversion in HeqUMalloc.
      simpl in *.
      destruct HeqUMalloc as [uM [uAMB [J1 [J2 [J3 [J4
                             [J5 [J6 [J7 [J8 J9]]]]]]]]]].
      inversion H. subst. clear H. simpl in *.
      exists uM, uAMB, ST.

      (* The 1st conjunct *)
      split.
      inversion J1. subst. clear J1.
      auto.

      (* The 2nd conjunct *)
      split. auto.
      split. auto.
      split. auto.

      (* The 3rd conjunct *)
      split.
      intros l vp H1. destruct vp as [v pmd].
      unfold accessMemPmd in *.
      unfold updatePmds.
      unfold updatePmd.
      remember (accessMem uM l) as Access.
      destruct Access.
        inversion H1. subst. clear H1.
        symmetry in HeqAccess.
        assert (H := HeqAccess).
        apply J5 in H.
        rewrite H. auto.

        inversion H1.

      (* The 4th conjunct *)
      split.
      intros l H1 H2.
      unfold accessMemPmd in *.
      unfold updatePmds.
      unfold updatePmd.
      remember (accessMem uM l) as Access.
      destruct Access.
        inversion H2.

        symmetry in HeqAccess. clear H2.
        apply J6 in HeqAccess.
        rewrite HeqAccess. auto. auto.

      (* The 5th conjunct *)
      split.
      intros l H1.
      apply J7 in H1.
      unfold accessMemPmd.
      rewrite H1. auto.

      (* The 6th conjunct *)
      split.
      intros l H1.
      assert (H2 := H1).
      apply J8 in H2.
      unfold accessMemPmd.
      unfold updatePmds.
      unfold updatePmd.
      rewrite H2. auto.

      (* The 7th conjunct *)
      split. auto.

      (* The 8th conjunct *)
      apply getFreshSEntry__inversion in HeqGetFreshSEntry.
      destruct HeqGetFreshSEntry as [Heq1 [Heq2 [Heq3 Heq4]]].
      split. auto.
      split. auto.
      split. auto.
      split. auto.

      (* The 9th conjunct *)
      split.
      unfold addSnd.
      destruct Nat.eq_dec.
        auto.
        contradict n0. auto.

      (* The 10th conjunct *)
      intros a H1.
      unfold addSnd.
      destruct Nat.eq_dec.
        subst. contradict H1. auto.
        auto.

    (* umalloc is invalid *)
    inversion H.
  (* getFreshSEntry is invalid *)
  inversion H.
Qed.

Lemma malloc__umalloc_Some : forall E n E' b sa,
  malloc E n = Some (E', b, sa) ->
  umalloc (Env2uEnv E) n = Some (Env2uEnv E', b).
Proof.
  intros E n E' b sa H.
  unfold malloc in H.
  remember (umalloc (Env2uEnv E) n) as uEB.
  destruct E as [M G AMB [frs top lsa] PT ST].
  unfold Env2uEnv in *.
  unfold StackVar2uStackVar in *. simpl in *.
  destruct uEB.
  destruct p as [uE ub].
  remember (getFreshSEntry ST) as sa0.
  destruct sa0.
  inversion H. subst. clear H.
  destruct uE as [uM uG uAMB [ufrs utop]]. simpl.
  symmetry in HequEB.
  apply umalloc__inversion in HequEB.
  destruct HequEB as [uM1 [uAMB1 [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]]]].
  inversion J1; subst. auto.

  inversion H.

  remember (getFreshSEntry ST) as sa1.
  destruct sa1. inversion H. inversion H.
Qed.

(******************************************************************************)
(** * [free]                                                                  *)
(******************************************************************************)

Lemma free__inversion_Env : forall E loc M' G' AMB' S' PT' ST',
  free E loc = Some (MkEnv M' G' AMB' S' PT' ST') ->
  exists M AMB PT ST,
  (* The global and stack variables are unchanged. *)
  E = MkEnv M G' AMB S' PT ST.
Proof.
  intros E loc M' G' AMB' S' PT' ST' H.
  unfold free in H.
  remember (accessMemPmd (mem E) (pmdtable E) loc) as vp.
  remember (ufree (Env2uEnv E) loc) as uE'.
  destruct vp. destruct p as [v p].
    destruct p. destruct p as [[b e] sa].
    destruct E as [M G AMB [frs top lsa] PT ST].
    unfold Env2uEnv in *.
    unfold StackVar2uStackVar in *.
    simpl in *.
      destruct (Nat.eq_dec v b) as [v_is_b | v_not_b].
        destruct (eq_stat_dec (lookUpSndTableStat ST sa) heap) as
            [stat_is_heap | stat_not_heap].
          destruct uE'.
            inversion H. subst. clear H.
            symmetry in HequE'.
            destruct u as [uM uAMB uG uS].
            apply ufree__inversion in HequE'.
            destruct HequE' as [uM0 [uAMB0 [b0 [e0 [J1 [J2 [J3
                               [J4 [J5 [J6 J7]]]]]]]]]].
            simpl in *. inversion J1. subst. clear J1.
            exists uM0, uAMB0, PT, ST. auto.
            inversion H.
          inversion H.
        inversion H.
      inversion H.
    inversion H.
Qed.

Lemma free__inversion : forall E loc M' G' AMB' S' PT' ST',
  free E loc = Some (MkEnv M' G' AMB' S' PT' ST') ->
  exists M AMB PT ST b e e' sa,
  (* The global and stack variables are unchanged. *)
  E = MkEnv M G' AMB S' PT ST /\
  (* The deallocated block is [b, e). *)
  accessMem M loc = Some b /\ AMB b = Some e /\
  (* The addresses beyond the deallocated block are not affected. *)
  (forall l vp, l < b \/ l >= e -> l <> loc ->
     accessMemPmd M PT l = vp -> accessMemPmd M' PT' l = vp) /\
  (* The addresses inside the deallocated block were previously valid. *)
  (forall l, b <= l < e ->
     exists vp, accessMemPmd M PT l = Some vp) /\
  (* The addresses inside the deallocated block are invalid. *)
  (forall l, b <= l < e ->
     accessMemPmd M' PT' l = None) /\
  (* The deallocated block is above the base address and below the stack. *)
  baseAddress <= b /\ e <= E.(stackvar).(top) /\
  (* The deallocated block is removed from the block table. *)
  AMB' = removeAllocMemBlock AMB b /\
  (*! The pmd was previously (b, e', (heap, _)). *)
  accessMemPmd M PT loc = Some (b, Some (b, e', sa)) /\
  lookUpSndTableStat ST sa = heap /\
  (*! The pmd is updated to (0, 0, (invalid, _)). *)
  (loc < b \/ loc >= e ->
     accessMemPmd M' PT' loc = Some (b, Some (0, 0, sa))) /\
  PT' loc = Some (0, 0, sa) /\
  lookUpSndTableStat ST' sa = invalid /\
  (*! The pmds of other pointers are not affected. *)
  (forall l, l <> loc ->
     PT l = PT' l) /\
  (*! The other status nodes are not affected. *)
  (forall a, a <> sa ->
     ST a = ST' a)
  .
Proof.
  intros E loc M' G' AMB' S' PT' ST' H.
  unfold free in H.
  remember (ufree (Env2uEnv E) loc) as UFree.
  unfold Env2uEnv in HeqUFree.
  unfold StackVar2uStackVar in HeqUFree.
  destruct E as [M G AMB [frs top lsa] PT ST].
  simpl in *.
  remember (accessMemPmd M PT loc) as AccessMP.
  destruct AccessMP. destruct p as (v, p).
    destruct p. destruct p as (be, sa). destruct be as (b, e).
      (* accessMemPmd returns valid value and pmd, i.e., Some (v, Some p) *)
      symmetry in HeqAccessMP.
      destruct Nat.eq_dec as [v_is_b | v_not_b].
        (* v = b *)
        destruct (eq_stat_dec (lookUpSndTableStat ST sa) heap).
        (* lookUpSndTableStat ST sa = heap *)
        destruct UFree. destruct u as [uM' uG' uAMB' uS'].
          (* ufree is valid *)
          symmetry in HeqUFree.
          apply ufree__inversion in HeqUFree.
          simpl in *.
          destruct HeqUFree as [uM [uAMB [ub [ue [J1 [J2 [J3
                               [J4 [J5 [J6 [J7 [J8 J9]]]]]]]]]]]].
          inversion H. subst. clear H. simpl in *.

          inversion J1. subst. clear J1.
          assert (J10 := HeqAccessMP).
          apply accessMemPmd__accessMem_Some in J10.
          rewrite J2 in J10. inversion J10. subst. clear J10.

          exists uM, uAMB, PT, ST, b, ue, e, sa.

          (* The 1st conjunct *)
          split. auto.

          (* The 2nd conjunct *)
          split. auto.
          split. auto.

          (* The 3rd conjunct *)
          split.
          intros l vp H1 H2 H3.
          unfold accessMemPmd in *.
          unfold updatePmd.
          remember (accessMem uM l) as AccessM.
          destruct AccessM.
            symmetry in HeqAccessM.
            rewrite J4 in HeqAccessM.
              rewrite HeqAccessM.
              destruct Nat.eq_dec as [l_is_loc | l_not_loc].
                subst. contradict H2. auto.
                auto.
              auto.

            symmetry in HeqAccessM.
            rewrite J4 in HeqAccessM.
              rewrite HeqAccessM. auto.
              auto.

          (* The 4th conjunct *)
          split.
          intros l H1.
          apply J5 in H1.
          destruct H1 as [v H1].
          unfold accessMemPmd.
          rewrite H1.
          exists (v, PT l). auto.

          (* The 5th conjunct *)
          split.
          intros l H1.
          apply J6 in H1.
          unfold accessMemPmd.
          rewrite H1. auto.

          (* The 6th conjunct *)
          split. auto.
          split. auto.

          (* The 7th conjunct *)
          split. auto.

          (* The 8th conjunct *)
          split.
          unfold accessMemPmd.
          auto.

          split. auto.

          (* The 9th conjunct *)
          split.
          intros H1.
          apply accessMemPmd__accessMem_Some in HeqAccessMP.
          rewrite J4 in HeqAccessMP.
            unfold accessMemPmd.
            unfold updatePmd.
            rewrite HeqAccessMP.
            destruct Nat.eq_dec.
              auto.
              contradict n. auto.
            auto.

          split.
          unfold updatePmd.
          destruct eq_nat_dec as [l_is_loc | l_not_loc].
            auto.
            contradict l_not_loc. auto.

          split.
          unfold lookUpSndTableStat.
          unfold updateSndStat.
          destruct Nat.eq_dec.
            destruct (ST sa). destruct s.
              auto.
              auto.
            contradict n. auto.

          (* The 10th conjunct *)
          split.
          intros l H2.
          unfold updatePmd.
          destruct eq_nat_dec as [l_is_loc | l_not_loc].
            subst. contradict H2. auto.
            auto.

          (* The 11th conjunct *)
          intros a H1.
          unfold updateSndStat.
          destruct Nat.eq_dec.
            subst. contradict H1. auto.
            auto.

        (* ufree is invalid *)
        inversion H.
        (* lookUpSndTableStat ST sa <> heap *)
        inversion H.
      (* v <> b *)
      inversion H.
    (* pmd is invalid *)
    inversion H.
  (* value is invalid *)
  inversion H.
Qed.

Lemma free__ufree_Some : forall E loc E',
  free E loc = Some E' ->
  ufree (Env2uEnv E) loc = Some (Env2uEnv E').
Proof.
  intros E loc E' H.
  unfold free in H.
  remember (accessMemPmd (mem E) (pmdtable E) loc) as vp.
    destruct vp. destruct p as [v p].
      destruct p. destruct p as [[b e] sa].
        destruct (Nat.eq_dec v b) as [v_is_b | v_not_b].
          destruct (eq_stat_dec (lookUpSndTableStat (sndtable E) sa) heap)
              as [stat_is_heap | stat_not_heap].
          remember (ufree (Env2uEnv E) loc) as uE'.
            destruct uE'.
            destruct E as [M G AMB [frs top lsa] PT ST].
            destruct E' as [M' G' AMB' [frs' top' lsa'] PT' ST'].
            destruct u as [uM uG uAMB [ufrs utop]].
            unfold Env2uEnv in *.
            unfold StackVar2uStackVar in *.
            simpl in *.
            symmetry in HequE'.
            apply ufree__inversion in HequE'.
            destruct HequE' as [uM2 [uAMB2 [b2 [e2
                               [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]]]]]].
            simpl in *.
            inversion J1. subst. clear J1.
            inversion H. subst. clear H. auto.

            inversion H.
            inversion H.
            inversion H.
            inversion H.
            inversion H.
Qed.

(******************************************************************************)
(** * [createFrame]                                                           *)
(******************************************************************************)

Lemma createFrame__inversion : forall E fr E',
  createFrame E fr = Some E' ->
  exists F' sa,
  (* The global variables and allocated blocks are unchanged. *)
  E.(globalvar) = E'.(globalvar) /\
  E.(amb) = E'.(amb) /\
  (* The created frame F' is instantiated from fr,
     is above the base address and strictly below the original stack. *)
  head (E'.(stackvar).(frames)) = Some F' /\
  Frame2frame F' = fr /\
  StackVar2frame (E'.(stackvar)) = fr /\
  (forall v t, fr v = Some t ->
     exists l, lookUpStackVar E'.(stackvar) v = Some (l, t, sa) /\
               F'.(from) <= l < F'.(to)) /\
  F'.(from) = E'.(stackvar).(top) /\
  F'.(to) = E.(stackvar).(top) /\
  F'.(s_sa) = sa /\
  tail (E'.(stackvar).(frames)) = E.(stackvar).(frames) /\
  baseAddress < E'.(stackvar).(top) < E.(stackvar).(top) /\
  E'.(stackvar).(l_sa) = F'.(s_sa) /\
  (* The values at valid addresses are not affected. *)
  (forall l vp,
     accessMemPmd E.(mem) E.(pmdtable) l = Some vp ->
     accessMemPmd E'.(mem) E'.(pmdtable) l = Some vp) /\
  (* The invalid addresses beyond the created frame are still invalid. *)
  (forall l, l < F'.(from) \/ l >= F'.(to) ->
     accessMemPmd E.(mem) E.(pmdtable) l = None ->
     accessMemPmd E'.(mem) E'.(pmdtable) l = None) /\
  (* The addresses inside the created frame were previously invalid. *)
  (forall l, F'.(from) <= l < F'.(to) ->
     accessMemPmd E.(mem) E.(pmdtable) l = None) /\
  (* The addresses inside the created frame are valid and filled with 0. *)
  (forall l, F'.(from) <= l < F'.(to) ->
     accessMemPmd E'.(mem) E'.(pmdtable) l = Some (0, E'.(pmdtable) l)) /\
  (* The created frame is well-formed. *)
  wfFrameNoOverlapped F' /\
  (*! The pmd table is not affected. *)
  E.(pmdtable) = E'.(pmdtable) /\
  (*! The allocated status node indicates the stack storage. *)
  E.(sndtable) sa = None /\ sa <> 0 /\ sa <> f_sa /\ sa <> g_sa /\
  E'.(sndtable) sa = Some (stack, 1) /\
  lookUpSndTableStat E'.(sndtable) sa = stack /\
  (*! The other status nodes are not affected. *)
  (forall a, a <> sa ->
     E.(sndtable) a = E'.(sndtable) a)
  .
Proof.
  intros E fr E' H.
  unfold createFrame in H.
  remember (ucreateFrame (Env2uEnv E) fr) as UCreateFrame.
  unfold Env2uEnv in HeqUCreateFrame.
  unfold StackVar2uStackVar in HeqUCreateFrame.
  destruct E as [M G AMB [frs top lsa] PT ST].
  destruct E' as [M' G' AMB' [frs' top' lsa'] PT' ST'].
  simpl in *.
  remember (getFreshSEntry ST) as GetFreshSEntry.
  destruct GetFreshSEntry.
    symmetry in HeqGetFreshSEntry.
    destruct UCreateFrame. destruct u as [uM' uG' uAMB' uS'].
      (* Both getFreshSEntry and ucreateFrame are valid *)
      symmetry in HeqUCreateFrame.
      apply ucreateFrame__inversion in HeqUCreateFrame.
      simpl in *.
      destruct HeqUCreateFrame as [uF' [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9
                                  [J10 [J11 [J12 [J13 [J14 J15]]]]]]]]]]]]]]].
      rewrite J3 in H.
      inversion H. subst. clear H. simpl in *.
      exists (MkFrame (ufdata uF') (ufrom uF') (uto uF') lsa'), lsa'.

      (* The 1st conjunct *)
      split. auto.
      split. auto.

      (* The 2nd conjunct *)
      split. auto.
      split. auto.
      split. auto.

      split.
      intros v t H1.
      apply J6 in H1.
      destruct H1 as [l [H1 H2]].
      unfold lookUpuStackVar in H1.
      rewrite J3 in H1.
      unfold lookUpuFrame in H1.
      exists l.
      split.
        unfold lookUpStackVar. simpl.
        destruct ufdata. destruct p.
          inversion H1. auto.
          inversion H1.
        auto.

      split. auto.
      split. auto.
      split. auto.
      split. auto.
      split. auto.
      split. auto.

      (* The 3rd conjunct *)
      split.
      intros l vp H1.
      destruct vp as [v pmd].
      unfold accessMemPmd in *.
      unfold updatePmds.
      unfold updatePmd.
      remember (accessMem M l) as Access.
      destruct Access.
        inversion H1. subst. clear H1.
        symmetry in HeqAccess.
        assert (H := HeqAccess).
        apply J11 in H. rewrite H. clear H.
        auto.
        inversion H1.

      (* The 4th conjunct *)
      split.
      intros l H1 H2.
      unfold accessMemPmd in *.
      unfold updatePmds.
      unfold updatePmd.
      remember (accessMem M l) as Access.
      destruct Access.
        inversion H2.

        symmetry in HeqAccess.
        apply J12 in HeqAccess.
        rewrite HeqAccess.
        auto.
        auto.

      (* The 5th conjunct *)
      split.
      intros l H1.
      simpl in H1.
      apply J13 in H1.
      unfold accessMemPmd.
      rewrite H1.
      auto.

      (* The 6th conjunct *)
      split.
      intros l H1.
      simpl in H1.
      assert (H := H1).
      apply J14 in H.
      unfold accessMemPmd.
      unfold updatePmds.
      unfold updatePmd.
      rewrite H.
      auto.

      (* The 7th conjunct *)
      split. auto.

      (* The 8th conjunct *)
      split. auto.

      (* The 9th conjunct *)
      apply getFreshSEntry__inversion in HeqGetFreshSEntry.
      destruct HeqGetFreshSEntry as [Heq1 [Heq2 [Heq3 Heq4]]].
      split. auto.
      split. auto.
      split. auto.
      split. auto.

      split.
      unfold addSnd.
      destruct Nat.eq_dec.
        auto.
        contradict n. auto.

      split.
      unfold lookUpSndTableStat.
      unfold addSnd.
      destruct Nat.eq_dec.
        auto.
        destruct (ST lsa'). destruct s.
          contradict n. auto.
          contradict n. auto.

      (* The 10th conjunct *)
      intros a H1.
      unfold addSnd.
      destruct Nat.eq_dec.
        subst. contradict H1. auto.
        auto.

    (* ucreateFrame is invalid *)
    inversion H.
  (* getFreshSEntry is invalid *)
  inversion H.
Qed.

Lemma createFrame__ucreateFrame_Some : forall E fr E',
  createFrame E fr = Some E' ->
  ucreateFrame (Env2uEnv E) fr = Some (Env2uEnv E').
Proof.
  intros E fr E' H.
  unfold createFrame in H.
  remember (ucreateFrame (Env2uEnv E) fr) as uE'.
  destruct E as [M G AMB [frs top lsa] PT ST].
  destruct E' as [M' G' AMB' [frs' top' lsa'] PT' ST'].
  unfold Env2uEnv in *.
  unfold StackVar2uStackVar in *. simpl in *.
  destruct uE'.
    destruct u as [uM uG uAMB [ufrs utop]]. simpl in *.
    remember (getFreshSEntry ST) as sa.
    destruct sa.
      destruct ufrs. simpl in *.
        inversion H.

        inversion H. subst. clear H.
        unfold Frames2uFrames.
        unfold Frame2uFrame. simpl.
        symmetry in HequE'.
        apply ucreateFrame__inversion in HequE'.
        simpl in *.
        destruct HequE' as [uF' [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 [J10
            [J11 [J12 [J13 [J14 J15]]]]]]]]]]]]]]]. subst.
        inversion J3. subst. clear J3.
        destruct uF' as [ufdata' ufrom' uto'].
        unfold Frames2uFrames.
        unfold Frame2uFrame.
        simpl. auto.

      inversion H.

    remember (getFreshSEntry ST) as sa.
    destruct sa.
      inversion H.
      inversion H.
Qed.

(******************************************************************************)
(** * [destroyFrame]                                                          *)
(******************************************************************************)

Lemma destroyFrame__inversion : forall E E',
  destroyFrame E = Some E' ->
  exists fr,
  (* The global variables and allocated blocks are unchanged. *)
  E.(globalvar) = E'.(globalvar) /\
  E.(amb) = E'.(amb) /\
  (* The destroyed frame fr is the head frame of the stack. *)
  head (E.(stackvar).(frames)) = Some fr /\
  fr.(to) = E'.(stackvar).(top) /\
  tail (E.(stackvar).(frames)) = E'.(stackvar).(frames) /\
  (* The addresses beyond the destroyed frame are not affected. *)
  (forall l vp, l < fr.(from) \/ l >= fr.(to) ->
     accessMemPmd (mem E) (pmdtable E) l = vp ->
     accessMemPmd (mem E') (pmdtable E') l = vp) /\
  (* The addresses inside the destroyed frame were previously valid. *)
  (forall l, fr.(from) <= l < fr.(to) ->
     exists v, accessMemPmd (mem E) (pmdtable E) l = Some v) /\
  (* The addresses inside the destroyed frame are invalid. *)
  (forall l, fr.(from) <= l < fr.(to) ->
     accessMemPmd (mem E') (pmdtable E') l = None) /\
  (*! The stack stores the status node address of the top frame. *)
  (forall F', head (E'.(stackvar).(frames)) = Some F' ->
     E'.(stackvar).(l_sa) = F'.(s_sa)) /\
  (head (E'.(stackvar).(frames)) = None ->
     E'.(stackvar).(l_sa) = 0) /\
  (*! The pmd table is not affected. *)
  E.(pmdtable) = E'.(pmdtable) /\
  (*! The pmd was previously (_, _, (stack, _)). *)
  lookUpSndTableStat E.(sndtable) fr.(s_sa) = stack /\
  (*! The pmd is updated to (_, _, (invalid, _)). *)
  lookUpSndTableStat E'.(sndtable) fr.(s_sa) = invalid /\
  (*! The other status nodes are not affected. *)
  (forall a, a <> fr.(s_sa) ->
     E.(sndtable) a = E'.(sndtable) a)
  .
Proof.
  intros E E' H.
  unfold destroyFrame in H.
  remember (udestroyFrame (Env2uEnv E)) as UDestroyFrame.
  unfold Env2uEnv in HeqUDestroyFrame.
  unfold StackVar2uStackVar in HeqUDestroyFrame.
  destruct E as [M G AMB [frs top lsa] PT ST].
  destruct E' as [M' G' AMB' S' PT' ST'].
  simpl in *.
  remember (head frs) as FirstFrame.
  destruct FirstFrame.
    (* The first frame in E is valid *)
    symmetry in HeqFirstFrame.
    destruct (eq_stat_dec (lookUpFrameStat f ST) stack).
    (* lookUpFrameStat fr ST = stack *)
    destruct UDestroyFrame. destruct u as [uM' uG' uAMB' uS'].
      (* udestroyFrame is valid *)
      symmetry in HeqUDestroyFrame.
      apply udestroyFrame__inversion in HeqUDestroyFrame.
      simpl in *.
      destruct HeqUDestroyFrame as [uF [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]]].
      remember (head (tail frs)) as SecondFrame.
      destruct SecondFrame.
        (**** The second frame in E is valid ****)
        symmetry in HeqSecondFrame.
        inversion H. subst. clear H. simpl in *.

        (* The frame list [fr frs] := [fr [f0 ...]] contains
           at least one frame fr *)
        destruct frs.
          simpl in *. inversion HeqFirstFrame.
          simpl in *. inversion HeqFirstFrame. inversion J3.
          subst. clear HeqFirstFrame J3. simpl in *.

        exists f.

        (* The 1st conjunct *)
        split. auto.
        split. auto.

        (* The 2nd conjunct *)
        split. auto.
        split. auto.
        split. auto.

        (* The 3rd conjunct *)
        split.
        intros l vp H1 H2.
        unfold accessMemPmd in *.
        remember (accessMem M l) as Access.
        symmetry in HeqAccess.
        apply J6 in HeqAccess.
        rewrite HeqAccess.
        auto.
        auto.

        (* The 4th conjunct *)
        split.
        intros l H1.
        unfold accessMemPmd.
        apply J7 in H1.
        destruct H1 as [v H1].
        rewrite H1.
        exists (v, PT' l).
        auto.

        (* The 5th conjunct *)
        split.
        intros l H1.
        unfold accessMemPmd.
        apply J8 in H1.
        rewrite H1.
        auto.

        (* The 6th conjunct *)
        split.
        intros F' H.
        rewrite HeqSecondFrame in H.
        inversion H.
        auto.

        split.
        intro H.
        rewrite HeqSecondFrame in H.
        inversion H.

        (* The 7th conjunct *)
        split. auto.

        (* The 8th conjunct *)
        split.
        unfold lookUpSndTableStat.
        unfold lookUpFrameStat in e.
        auto.

        (* The 9th conjunct *)
        split.
        unfold lookUpSndTableStat.
        unfold updateSndStat.
        unfold updateSndDec.
        destruct Nat.eq_dec.
          destruct (ST (s_sa f)). destruct s.
            auto.
            auto.
          destruct (ST (s_sa f)). destruct s.
            contradict n. auto.
            auto.

        (* The 10th conjunct *)
        intros a H1.
        unfold updateSndStat.
        unfold updateSndDec.
        destruct Nat.eq_dec.
          destruct Nat.eq_dec.
            destruct (ST (s_sa f)). destruct s.
              contradict H1. auto.
              contradict H1. auto.
            contradict H1. auto.
          auto.

        (**** The second frame in E is invalid ****)
        symmetry in HeqSecondFrame.
        inversion H. subst. clear H. simpl in *.

        (* The frame list [fr frs] := [f] contains
           at least one frame fr *)
        destruct frs.
          simpl in *. inversion HeqFirstFrame.
          simpl in *. inversion HeqFirstFrame. inversion J3.
          subst. clear HeqFirstFrame J3. simpl in *.

        exists f.

        (* The 1st conjunct *)
        split. auto.
        split. auto.

        (* The 2nd conjunct *)
        split. auto.
        split. auto.
        split. auto.

        (* The 3rd conjunct *)
        split.
        intros l vp H1 H2.
        unfold accessMemPmd in *.
        remember (accessMem M l) as Access.
        symmetry in HeqAccess.
        apply J6 in HeqAccess.
        rewrite HeqAccess.
        auto.
        auto.

        (* The 4th conjunct *)
        split.
        intros l H1.
        unfold accessMemPmd.
        apply J7 in H1.
        destruct H1 as [v H1].
        rewrite H1.
        exists (v, PT' l).
        auto.

        (* The 5th conjunct *)
        split.
        intros l H1.
        unfold accessMemPmd.
        apply J8 in H1.
        rewrite H1.
        auto.

        (* The 6th conjunct *)
        split.
        intros F' H.
        rewrite HeqSecondFrame in H.
        inversion H.

        split.
        auto.

        (* The 7th conjunct *)
        split. auto.

        (* The 8th conjunct *)
        split.
        unfold lookUpSndTableStat.
        unfold lookUpFrameStat in e.
        auto.

        (* The 9th conjunct *)
        split.
        unfold lookUpSndTableStat.
        unfold updateSndDec.
        unfold updateSndStat.
        destruct Nat.eq_dec.
          destruct (ST (s_sa f)). destruct s.
            auto.
            auto.
          contradict n. auto.

        (* The 10th conjunct *)
        intros a H1.
        unfold updateSndStat.
        unfold updateSndDec.
        destruct Nat.eq_dec.
          destruct (ST (s_sa f)). destruct s.
            contradict H1. auto.
            contradict H1. auto.
          auto.

      (* udestroyFrame is invalid *)
      inversion H.
      (* lookUpFrameStat fr ST <> stack *)
      inversion H.
    (* The first frame in E is invalid *)
    inversion H.
Qed.

Lemma destroyFrame__udestroyFrame_Some : forall E E',
  destroyFrame E = Some E' ->
  udestroyFrame (Env2uEnv E) = Some (Env2uEnv E').
Proof.
  intros E E' H.
  unfold destroyFrame in H.
  remember (udestroyFrame (Env2uEnv E)) as uE'.
  destruct uE'.
    destruct E as [M G AMB [frs top lsa] PT ST].
    destruct E' as [M' G' AMB' [frs' top' lsa'] PT' ST'].
    destruct u as [uM uG uAMB [ufrs utop]].
    unfold Env2uEnv in *.
    unfold StackVar2uStackVar in *. simpl in *.
    remember (head frs) as J.
    destruct J.
      destruct (eq_stat_dec (lookUpFrameStat f ST) stack) as [J0 | J0].
        symmetry in HequE'.
        apply udestroyFrame__inversion in HequE'.
        destruct HequE' as [uF [J1 [J2 [J3 [J4 [J5 [J6 [J7 J8]]]]]]]].
        simpl in *. subst.
        remember (head (tail frs)) as J.
        destruct J.
          inversion H; subst. clear H.
          destruct frs; simpl; auto.

          inversion H; subst. clear H.
          destruct frs; simpl; auto.

        inversion H.

      inversion H.

    destruct (head (frames (stackvar E))).
      destruct (eq_stat_dec (lookUpFrameStat f (sndtable E)) stack).
        inversion H.
        inversion H.
      inversion H.
Qed.

(******************************************************************************)
(** * Decidable primitives                                                    *)
(******************************************************************************)

Lemma isPtr_dec : forall t,
  isPtr t \/ ~isPtr t.
Proof.
  intros.
  destruct t.
  simpl in *. auto.
  simpl in *. auto.
Qed.

Lemma accessMem_dec : forall M loc,
  (exists v, accessMem M loc = Some v) \/
  accessMem M loc = None.
Proof.
  intros.
  destruct (accessMem M loc).
  left. exists v. auto.
  right; auto.
Qed.

Lemma storeMem_dec : forall M loc v,
  (exists M', storeMem M loc v = Some M') \/
  storeMem M loc v = None.
Proof.
  intros.
  destruct (storeMem M loc v).
  left. exists m. auto.
  right; auto.
Qed.

Lemma check_dpv_dec : forall ST v pmd a,
  check_dpv ST v pmd a \/ ~check_dpv ST v pmd a.
Proof.
  intros.
  destruct v.
  Case "v = 0".
    destruct pmd as [[b e] sa].
    destruct a.
    SCase "Atype is Int".
      unfold check_dpv.
      simpl. auto.

    SCase "Atype is Pointer".
      destruct b.
      SSCase "b = 0".
          destruct r.
          SSSCase "A_Pointer (R_AType a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct H as [H0 [H1 H2]]. contradict H0. auto.

          SSSCase "A_Pointer (R_Struct a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct H as [H0 [H1 H2]]. contradict H0. auto.

          SSSCase "A_Pointer (R_Name a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct (typeTable c).
            destruct H as [H0 [H1 H2]]. contradict H0. auto.

            auto.

          SSSCase "A_Pointer (R_Void a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            auto.

          SSSCase "A_Pointer (R_Func a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            auto.
      SSCase "b <> 0".
          destruct r.
          SSSCase "A_Pointer (R_AType a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. lia.

          SSSCase "A_Pointer (R_Struct a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. lia.

          SSSCase "A_Pointer (R_Name a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct (typeTable c).
            destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. lia.

            auto.

          SSSCase "A_Pointer (R_Void a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            auto.

          SSSCase "A_Pointer (R_Func a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            auto.

  Case "v <> 0".
    destruct pmd as [[b e] sa].
    destruct a.
    SCase "Atype is Int".
      unfold check_dpv.
      auto.

    SCase "Atype is Pointer".
       destruct b.
       SSCase "b = 0".
          destruct r.
          SSSCase "A_Pointer (R_AType a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct H as [H0 [H1 H2]]. contradict H0. auto.

          SSSCase "A_Pointer (R_Struct a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct H as [H0 [H1 H2]]. contradict H0. auto.

          SSSCase "A_Pointer (R_Name a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            destruct (typeTable c).
            destruct H as [H0 [H1 H2]]. contradict H0. auto.

            auto.

          SSSCase "A_Pointer (R_Void a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            auto.

          SSSCase "A_Pointer (R_Func a)".
            right. unfold not. intros.
            unfold check_dpv in H.
            auto.

        SSCase "b <> 0".
          destruct r.
          destruct (le_gt_dec (S b) (S v)).
          SSSCase "S b <= S v".

            SSSSCase "S v + sizeOfAType a <= e".
              destruct (le_gt_dec ((S v) + sizeOfAType a) e).
              SSSSSCase "sa = 0".
                destruct (Nat.eq_dec sa 0).
                SSSSSSCase "A_Pointer (R_AType a)".
                  right. unfold not. intros.
                  unfold check_dpv in H.
                  destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                  rewrite e0 in H4. contradict H4. auto.

                  destruct (eq_stat_dec (lookUpSndTableStat ST sa) invalid).

                    right. unfold not. intros.
                    unfold check_dpv in H.
                    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                    rewrite e0 in H5. contradict H5. auto.

                  destruct (eq_stat_dec (lookUpSndTableStat ST sa) function).

                    right. unfold not. intros.
                    unfold check_dpv in H.
                    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                    rewrite e0 in H6. contradict H6. auto.

                    left. unfold check_dpv; try solve [split; auto | auto].

                    right. unfold not. intros.
                    unfold check_dpv in H.
                    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                    lia.

                    right. unfold not. intros.
                    unfold check_dpv in H.
                    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                    lia.

          destruct (le_gt_dec (S b) (S v)).
          SSSCase "S b <= S v".
            SSSSCase "S v + sizeOfAType a <= e".
              destruct (le_gt_dec ((S v) + sizeOfStruct s) e ).
              SSSSSCase "sa = 0".
                destruct (Nat.eq_dec sa 0).
                SSSSSSCase "A_Pointer (R_Struct s)".
                  right. unfold not. intros.
                  unfold check_dpv in H.
                  destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                  rewrite e0 in H4. contradict H4. auto.

                  destruct (eq_stat_dec (lookUpSndTableStat ST sa) invalid).

                    right. unfold not. intros.
                    unfold check_dpv in H.
                    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                    rewrite e0 in H5. contradict H5. auto.

                  destruct (eq_stat_dec (lookUpSndTableStat ST sa) function).

                    right. unfold not. intros.
                    unfold check_dpv in H.
                    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                    rewrite e0 in H6. contradict H6. auto.

                    left. unfold check_dpv; try solve [split; auto | auto].

                    right. unfold not. intros.
                    unfold check_dpv in H.
                    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                    lia.

                    right. unfold not. intros.
                    unfold check_dpv in H.
                    destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                    lia.

        unfold check_dpv.
        destruct (typeTable c).
        destruct (le_gt_dec (S b) (S v)).
        SSSCase "S b <= S v".
          destruct (le_gt_dec ((S v) + sizeOfStruct s) e ).
          SSSSCase "S v + sizeOfAType a <= e".
            destruct (Nat.eq_dec sa 0).
            SSSSSCase "sa = 0".
              SSSSSSCase "A_Pointer (R_Name s)".
              right. unfold not. intros.
              destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
              rewrite e0 in H4. contradict H4. auto.

              destruct (eq_stat_dec (lookUpSndTableStat ST sa) invalid).

                right. unfold not. intros.
                destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                rewrite e0 in H5. contradict H5. auto.

              destruct (eq_stat_dec (lookUpSndTableStat ST sa) function).

                right. unfold not. intros.
                destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                rewrite e0 in H6. contradict H6. auto.

                left; try solve [split; auto | auto].

                right. unfold not. intros.
                destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                lia.

                right. unfold not. intros.
                destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
                lia.

                auto.

                unfold check_dpv.
                auto.

                unfold check_dpv.
                auto.
Qed.

Lemma check_dpfv_dec : forall ST v pmd,
  check_dpfv ST v pmd \/ ~check_dpfv ST v pmd.
Proof.
  intros.
  destruct v.
  Case "v = 0".
    destruct pmd as [[b e] sa].
    right. unfold not. intros.
    unfold check_dpfv in H.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    rewrite H2 in H1.
    contradict H1. auto.

  Case "v <> 0".
    destruct pmd as [[b e] sa].
    destruct b.
    SCase "b = 0".
      right. unfold not. intros.
      unfold check_dpfv in H.
      destruct H as [H1 [H2 [H3 [H4 H5]]]].
      contradict H1. auto.
    SSCase "b <> 0".
      unfold check_dpfv.
      destruct (Nat.eq_dec (S b) (S v)).
      SSSCase "S b = S v".
        destruct (Nat.eq_dec sa 0).
        SSSSSCase "sa = 0".
            right. unfold not. intros.
            destruct H as [H1 [H2 [H3 [H4 H5]]]].
            apply H3 in e1.
            auto.
        SSSSSCase "sa <> 0".
            destruct (eq_stat_dec (lookUpSndTableStat ST sa) invalid).
                right. unfold not. intros.
                destruct H as [H1 [H2 [H3 [H4 H5]]]].
                apply H4 in e1.
                auto.

            destruct (eq_stat_dec (lookUpSndTableStat ST sa) function).
                left; try solve [split; auto | auto].

                right. unfold not. intros.
                destruct H as [H1 [H2 [H3 [H4 H5]]]].
                rewrite H5 in n1.
                contradict n1. auto.

      SSSCase "S b <> S v".
        right. unfold not. intros.
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        rewrite H2 in n.
        contradict n. auto.
Qed.

Lemma check_free_dec : forall ST v pmd,
  check_free ST v pmd \/ ~check_free ST v pmd.
Proof.
  intros.
  destruct v.
  Case "v = 0".
    destruct pmd as [[b e] sa].
    right. unfold not. intros.
    unfold check_free in H.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    rewrite H2 in H1.
    contradict H1. auto.

  Case "v <> 0".
    destruct pmd as [[b e] sa].
    destruct b.
    SCase "b = 0".
      right. unfold not. intros.
      unfold check_free in H.
      destruct H as [H1 [H2 [H3 [H4 H5]]]].
      contradict H1. auto.
    SCase "b <> 0".
      unfold check_free.
      destruct (Nat.eq_dec (S b) (S v)).
      SSCase "S b = S v".
        destruct (Nat.eq_dec sa 0).
        SSSCase "sa = 0".
          right. unfold not. intros.
          destruct H as [H1 [H2 [H3 [H4 H5]]]].
          apply H3 in e1.
          auto.

        SSSCase "sa <> 0".
          destruct (eq_stat_dec (lookUpSndTableStat ST sa) invalid).
            right. unfold not. intros.
            destruct H as [H1 [H2 [H3 [H4 H5]]]].
            apply H4 in e1.
            auto.

            destruct (eq_stat_dec (lookUpSndTableStat ST sa) heap).
              left; try solve [split; auto | auto].

              right. unfold not. intros.
              destruct H as [H1 [H2 [H3 [H4 H5]]]].
              rewrite H5 in n1.
              contradict n1. auto.

      SSCase "S b <> S v".
        right. unfold not. intros.
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        rewrite H2 in n.
        contradict n. auto.
Qed.

Lemma check_ml_dec : forall ST sa,
  check_ml ST sa \/ ~check_ml ST sa.
Proof.
  intros.
  unfold check_ml.
  destruct (Nat.eq_dec sa 0).
    left. unfold not.
    intros J1 J2.
    apply J1 in e.
    auto.

    destruct (lookUpSndTableCount ST sa).
      destruct (eq_stat_dec (lookUpSndTableStat ST sa)  heap).
        destruct (le_gt_dec c 1).
         right.
         unfold not.
         intros.
         assert (lookUpSndTableStat ST sa = heap /\ c<=1). auto.
         assert (sa = 0 -> False).
         intros. rewrite H1 in n.
         contradict n. auto.
         apply H. auto. auto.

         left. intros. unfold not.
         intros.
         destruct H0 as [H1 H2].
         lia.

         left. intros. unfold not.
         intros.
         destruct H0 as [H1 H2].
         rewrite H1 in n0.
         contradict n0. auto.

         left. intros. unfold not.
         intros. destruct H0 as [H1 H2].
         auto.
Qed.

Lemma accessMemPmd_dec : forall M PT loc,
  (exists vp, accessMemPmd M PT loc = Some vp) \/
  accessMemPmd M PT loc = None.
Proof.
  intros.
  destruct (accessMemPmd M PT loc) as [vp0 | ].
  left. exists vp0. auto.
  right. auto.
Qed.

Lemma storeMemPmd_dec : forall M PT ST loc vp,
  (exists MPS, storeMemPmd M PT ST loc vp = Some MPS) \/
  storeMemPmd M PT ST loc vp = None.
Proof.
  intros.
  destruct (storeMemPmd M PT ST loc vp) as [MPS | ].
  left. exists MPS. auto.
  right. auto.
Qed.

Lemma malloc_dec : forall E n,
  (exists E', exists b, exists sa, malloc E n = Some (E', b, sa)) \/
  malloc E n = None.
Proof.
  intros.
  destruct (malloc E n).
  left. destruct p. destruct p.
  exists e, b, s. auto.
  right. auto.
Qed.

Lemma free_dec : forall E loc,
  (exists E', free E loc = Some E') \/ free E loc = None.
Proof.
  intros E loc.
  destruct (free E loc) as [E' | ].
  left. exists E'. auto.
  right. auto.
Qed.

Lemma createFrame_dec : forall E f,
  (exists E', createFrame E f = Some E') \/ createFrame E f = None.
Proof.
  intros.
  destruct (createFrame E f) as [E' | ].
  left. exists E'. auto.
  right. auto.
Qed.

Lemma destroyFrame_dec : forall E,
  (exists E', destroyFrame E = Some E') \/ destroyFrame E = None.
Proof.
  intros.
  destruct (destroyFrame E) as [E' | ].
  left. exists E'. auto.
  right. auto.
Qed.

(******************************************************************************)
(** * More lemmas for arithmetics                                             *)
(******************************************************************************)

Lemma nateq_plus_inv : forall n m i,
  n + i = m + i ->
  n = m.
Proof.
  intros. lia.
Qed.

Global Hint Resolve nateq_plus_inv : core.

Lemma neq_zero__ge_zero : forall n,
  n <> 0 -> n > 0.
Proof.
  intros n J.
  destruct n.
  contradict J; auto.
  lia.
Qed.

Global Hint Resolve neq_zero__ge_zero : core.

Lemma le_ge__eq : forall (i j : nat),
  i <= j ->
  j <= i ->
  i = j.
Proof.
  induction i.
    intros.
    destruct j.
    auto.
    contradict H0. lia.

    intros.
    destruct j.
    lia.
    assert (i<=j). lia.
    assert (j<=i). lia.
    assert (i=j). auto.
    subst. auto.
Qed.

Global Hint Resolve le_ge__eq : core.

Lemma lia_ex1 : forall a b c d,
  d <= a <= b - c ->
  c > 0 ->
  d <> 0 ->
  (b > c /\ a < b).
Proof.
  induction a; intros.
    assert (d = 0). clear H0 H1. lia.
    subst. contradict H1. auto.

    destruct (le_lt_dec b c).
    assert (b - c = 0). lia.
    rewrite H2 in H.
    contradict H. lia.

    split. auto. lia.
Qed.

Global Hint Resolve lia_ex1 : core.

Lemma overlapped_interval : forall b e b' e' i,
  b  <= i < e ->
  b' <= i < e' ->
  ((b <= b' /\ b' < e) \/ (b' <= b /\ b < e')).
Proof.
  intros b e b' e' i H1 H2.
  destruct (le_lt_dec b b').
  destruct (le_lt_dec e b'); auto.
  assert (i < i) as J. lia.
  contradict J; lia.

  destruct (le_lt_dec e' b); auto.
  assert (i < i) as J. lia.
  contradict J; lia.

  right. lia.
Qed.

Lemma overlapped_interval_sub : forall b e b' e' b0 e0,
  ((b' <= b0 < e') \/ (b0 <= b' < e0)) ->
  b <= b' -> b' < e' -> e' <= e ->
  ((b <= b0 < e) \/ (b0 <= b < e0)).
Proof.
  intros b e b' e' b0 e0 H1 H2 H3 H4.
  destruct H1 as [H1 | H1].
  left. lia.
  destruct (le_lt_dec b b0).
  left. lia.
  right. lia.
Qed.
