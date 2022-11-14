Require Import Compare_dec.
Require Import EqNat.
Require Import Lia.
Require Import List.
Require Import Mult.

Require Import Types.
Require Import Envs.
Require Import Syntax.
Require Import CSemantics.
Require Import ISemantics.
Require Import Axioms.
Require Import Tactics.
Require Import LibBehavior.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

(******************************************************************************)
(** *                     Properties of results                               *)
(******************************************************************************)

Lemma uROK__isnot__uError :
  ~uError uROK.
Proof.
  unfold uError. intro J. inversion J.
Qed.

Global Hint Resolve uROK__isnot__uError : core.

Lemma RAbort__is__Error : forall R,
  R = RAbort ->
  Error R.
Proof.
  unfold Error. intros. auto.
Qed.

Lemma Error__inversion : forall R,
  Error R ->
  R = ROK \/ R = RAbort \/ R = RSystemError.
Proof.
  intros R H.
  destruct R.
    unfold Error in H. destruct H as [H | H]. inversion H. inversion H.
    unfold Error in H. destruct H as [H | H]. inversion H. inversion H.
    inversion H. inversion H0.
    inversion H0.
    auto.
    auto.
Qed.

(******************************************************************************)
(** *            Backward behavior simulation                                 *)
(******************************************************************************)

(** We proved that if an instrumented program terminates successfully,
    the original C program will not cause any memory violation. *)

Lemma s_lhs__implies__us_lhs : forall E lhs loc sa t,
  s_lhs E lhs (RLoc (loc, sa)) t ->
  us_lhs (Env2uEnv E) lhs (uRLoc loc) t.
Proof.
  intros E lhs loc sa t H.
  remember (RLoc (loc, sa)) as RLS.
  generalize dependent loc.
  generalize dependent sa.
  (s_lhs_cases (induction H) Case).
  Case S_GVar.
    intros. inversion HeqRLS. subst. clear HeqRLS.
    apply uS_GVar.
      unfold StackVar2frame in H.
      unfold Frame2frame in H.
      unfold uStackVar2frame.
      unfold Env2uEnv.
      unfold uFrame2frame.
      simpl.
      unfold Frames2uFrames.
      unfold Frame2uFrame.
      destruct (frames (stackvar E)).
        simpl in *. auto.
        simpl in *. auto.
      auto.
      auto.
  Case S_SVar.
    intros. inversion HeqRLS. subst. clear HeqRLS.
    apply uS_SVar.
    unfold lookUpStackVar in H.
    destruct E as [M G AMB [frs top lsa] PT ST].
    unfold lookUpuStackVar.
    unfold Env2uEnv.
    unfold StackVar2uStackVar.
    simpl in *.
    unfold Frames2uFrames.
    unfold Frame2uFrame.
    destruct frs.
      simpl in *. inversion H.
      simpl in *.
      unfold lookUpFrame in H.
      destruct (fdata f vid).
        destruct p as [fl fa]. inversion H. subst. auto.
        inversion H.
    auto.
  Case S_Deref.
    intros. inversion HeqRLS. subst. clear HeqRLS.
    eapply uS_Deref. eauto.
    apply accessMemPmd__accessMem_Some in H0. auto.
  Case S_Deref_ErrorProp.
    intros. subst.
    unfold Error in H0.
    destruct H0 as [H0 | H0].
      inversion H0.
      inversion H0.
  Case S_Deref_Abort.
    intros. inversion HeqRLS.
  Case S_Deref_Abort_None.
    intros. inversion HeqRLS.
  Case S_StructPos.
    intros. inversion HeqRLS. subst. clear HeqRLS.
    eapply uS_StructPos.
      eauto.
      apply accessMemPmd__accessMem_Some in H0. auto.
      auto.
      auto.
  Case S_StructPos_ErrorProp.
    intros. subst.
    unfold Error in H0.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_StructPos_Abort.
    intros.
    inversion HeqRLS.
  Case S_StructPos_Abort_None.
    intros.
    inversion HeqRLS.
  Case S_NamePos.
    intros. inversion HeqRLS. subst.
    eapply uS_NamePos.
      eauto.
      eauto.
      apply accessMemPmd__accessMem_Some in H1. auto.
      auto.
      auto.
  Case S_NamePos_ErrorProp.
    intros. subst.
    unfold Error in H0.
    destruct H0 as [H0 | H0].
      inversion H0.
      inversion H0.
  Case S_NamePos_Abort.
    intros. inversion HeqRLS.
  Case S_NamePos_Abort_None.
    intros. inversion HeqRLS.
Qed.

Lemma s_lhs__cannot__RSystemError : forall E lhs R t,
  s_lhs E lhs R t ->
  R <> RSystemError.
Proof.
  intros E lhs R t H.
  (s_lhs_cases (induction H) Case);
    intro J; try solve [inversion J | auto].
Qed.

Lemma s_rhs__implies__us_rhs : forall E rhs v p t E',
  s_rhs E rhs (RVal (v, p)) t E' ->
  us_rhs (Env2uEnv E) rhs (uRVal v) t (Env2uEnv E').
Proof.
  intros E rhs v p t E' H.
  remember (RVal (v, p)) as RVP.
  generalize dependent v.
  generalize dependent p.
  (s_rhs_cases (induction H) Case).
  Case S_Const.
    intros. inversion HeqRVP. subst.
    auto.
  Case S_Size.
    intros. inversion HeqRVP. subst. clear HeqRVP.
    apply uS_Size. auto.
    auto.
  Case S_Fun.
    intros. inversion HeqRVP. subst. clear HeqRVP.
    apply uS_Fun with (c:=c)(fr:=fr). auto.
  Case S_Lhs.
    intros. inversion HeqRVP. subst. clear HeqRVP.
    apply uS_Lhs with (loc:=loc).
      apply s_lhs__implies__us_lhs in H. auto.
      apply accessMemPmd__accessMem_Some in H0. auto.
  Case S_Lhs_None.
    intros. inversion HeqRVP. subst. clear HeqRVP.
    apply uS_Lhs with (loc:=loc).
      apply s_lhs__implies__us_lhs in H. auto.
      apply accessMemPmd__accessMem_Some in H0. auto.
  Case S_Lhs_ErrorProp.
    intros.
    destruct H0 as [H0 | H0].
      subst. inversion HeqRVP.
      subst. inversion HeqRVP.
  Case S_Ref.
    intros. inversion HeqRVP. subst. clear HeqRVP.
    apply uS_Ref.
      apply s_lhs__implies__us_lhs in H. auto.
      auto.
  Case S_Ref_ErrorProp.
    intros.
    destruct H0 as [H0 | H0].
      subst. inversion HeqRVP.
      subst. inversion HeqRVP.
  Case S_Cast.
    intros. subst.
    destruct d as [v1 p1].
    inversion HeqRVP. clear HeqRVP.
    unfold dataCast in H2.
    assert (v1 = v) as EQ.
      destruct a'. destruct a.
        destruct p1. destruct p0. inversion H2. auto.
        destruct p1. destruct p0. inversion H2. auto.
        destruct p1. destruct p0. destruct a. destruct (le_lt_dec).
        inversion H2. auto.
        destruct (sizeOfRType r). inversion H2. auto.
        inversion H2. auto.
        inversion H2. auto.
    subst.
    apply uS_Cast with (a:=a).
      eauto.
      auto.
  Case S_Cast_ErrorProp.
    intros. subst.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_Add_Int_Int.
    intros.
    inversion HeqRVP. subst. clear HeqRVP.
    apply uS_Add_Int_Int with (E':=(Env2uEnv E')).
    apply IHs_rhs1 with (p:=pmd1). auto.
    apply IHs_rhs2 with (p:=pmd2). auto.
  Case S_Add_Int_Int_ErrorProp1.
    intros. subst.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_Add_Int_Int_ErrorProp2.
    intros. subst.
    destruct H1 as [H1 | H1].
    inversion H1.
    inversion H1.
  Case S_Add_Ptr_Int.
    intros.
    inversion HeqRVP. subst. clear HeqRVP.
    apply uS_Add_Ptr_Int with (E':=(Env2uEnv E')).
    apply IHs_rhs1 with (p:=p). auto. (** seems with p0:=p *)
    auto.
    auto.
    apply IHs_rhs2 with (p:=pmd2). auto.
  Case S_Add_Ptr_Int_ErrorProp1.
    intros. subst.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_Add_Ptr_Int_ErrorProp2.
    intros. subst.
    destruct H1 as [H1 | H1].
    inversion H1.
    inversion H1.
  Case S_Alloc.
    intros.
    inversion HeqRVP. subst. clear HeqRVP.
    apply uS_Alloc with (E':=(Env2uEnv E'))(n:=n)(size:=size).
    apply IHs_rhs with (p:=pmd). auto.
    auto.
    auto.
    auto.
    apply malloc__umalloc_Some in H3. auto.
  Case S_Alloc_ErrorProp.
    intros. subst.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_Alloc_OutofMem.
    intros.
    inversion HeqRVP.
Qed.

Lemma s_cmd__implies__us_cmd : forall E cmd E',
  s_cmd E cmd ROK E' ->
  us_cmd (Env2uEnv E) cmd uROK (Env2uEnv E').
Proof.
  intros E cmd E' H.
  remember ROK as R.
  (s_cmd_cases (induction H) Case).
  Case S_Skip.
    auto.
  Case S_Seq.
    apply uS_Seq with (E':=(Env2uEnv E')).
    auto.
    auto.
  Case S_Seq_ErrorProp1.
    subst.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_Seq_ErrorProp2.
    subst.
    destruct H1 as [H1 | H1].
    inversion H1.
    inversion H1.
  Case S_Assign_Ptr.
    subst.
    destruct d as [v p].
    unfold Env2uEnv. simpl.
    apply uS_Assign with (loc:=loc)(al:=al)(val:=v)(ar:=ar)(E':=Env2uEnv E').
      apply s_lhs__implies__us_lhs in H. auto.

      apply s_rhs__implies__us_rhs in H0. auto.

      unfold dataCast in H3.
      destruct p. destruct p. destruct ar. destruct al.
        apply storeMemPmd__storeMem_Some in H3. auto.
        destruct le_lt_dec.
          apply storeMemPmd__storeMem_Some in H3. auto.
          destruct sizeOfRType.
            apply storeMemPmd__storeMem_Some in H3. auto.
            apply storeMemPmd__storeMem_Some in H3. auto.
        apply storeMemPmd__storeMem_Some in H3. auto.

      auto.
      auto.
      auto.
  Case S_Assign_NPtr.
    subst.
    destruct d as [v p].
    unfold Env2uEnv. simpl.
    apply uS_Assign with (loc:=loc)(al:=al)(val:=v)(ar:=ar)(E':=Env2uEnv E').
      apply s_lhs__implies__us_lhs in H. auto.

      apply s_rhs__implies__us_rhs in H0. auto.

      unfold dataCast in H3.
      destruct p. destruct p. destruct ar. destruct al.
        simpl in H3. auto.
        destruct le_lt_dec. auto.
        destruct sizeOfRType.
          auto.
          auto.
        auto.

      auto.
      auto.
      auto.
  Case S_Assign_ErrorProp1.
    subst.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_Assign_ErrorProp2.
    subst.
    destruct H1 as [H1 | H1].
    inversion H1.
    inversion H1.
  Case S_Assign_Ptr_Abort.
    inversion HeqR.
  Case S_Call.
    subst.
    apply uS_Call with (fr:=fr)(c:=c)(E':=Env2uEnv E')
          (E'':=Env2uEnv E'')(loc:=loc)(a:=a)(E''':=Env2uEnv E''').
    apply s_rhs__implies__us_rhs in H. auto.
    auto.
    apply createFrame__ucreateFrame_Some in H2. auto.
    auto.
    auto.
    apply destroyFrame__udestroyFrame_Some in H5. auto.
  Case S_Call_ErrorProp1.
    subst.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_Call_ErrorProp2.
    subst.
    destruct H4 as [H4 | H4].
    inversion H4.
    inversion H4.
  Case S_Call_Error1.
    inversion HeqR.
  Case S_Call_Error2.
    inversion HeqR.
  Case S_Call_Abort.
    inversion HeqR.
  Case S_Free.
    apply uS_Free with (r:=r)(loc:=loc)(E':=Env2uEnv E').
    apply s_rhs__implies__us_rhs in H. auto.
    apply free__ufree_Some in H1. auto.
  Case S_Free_ErrorProp.
    subst.
    destruct H0 as [H0 | H0].
    inversion H0.
    inversion H0.
  Case S_Free_Error.
    inversion HeqR.
  Case S_Free_Abort.
    inversion HeqR.
Qed.

Lemma s_cmd__cannot__RVal_or_RLoc : forall E cmd R E',
  s_cmd E cmd R E' ->
  R = ROK \/ R = RAbort \/ R = RSystemError.
Proof.
  intros E cmd R E' H.
  (s_cmd_cases (induction H) Case);
    auto using Error__inversion.
Qed.
