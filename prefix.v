(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import
  lattice monoid rel kat_tac normalisation kleene kat rewriting.
Require Import Ensembles.
Require Import Relations.
From RC11 Require Import proprel_classic.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import rc11.

(** The file contains the definition and properties of execution prefixes *)

(** * Execution prefix *)

(** ** Definition *)

(** An execution [E'] is a prefix of an execution [E] if:

- The events of [E'] is a subset of the events of [E]
- The events of [E'] contain all the initialisation events of [E]
- The events of [E'] are closed with respect to [E.sb U E.rf] : [a] is an event
of [E'] whenever [b] is an event of [E'] and [a] and [b] are related by [sb] or
[rf] in execution [E] 
- All the relations between the events of [E'] are the relations on the events
of [E] restricted to the subparts of the relation relating elements of [E'] *)

Definition prefix (pre ex: Execution) : Prop :=
  (Included _ (evts pre) (evts ex)) /\
  (forall a b, (sb ex ⊔ rf ex) a b ->
               In _ (evts pre) b ->
               In _ (evts pre) a) /\
  (sb pre = [I (evts pre)] ⋅ (sb ex) ⋅ [I (evts pre)]) /\
  (rf pre = [I (evts pre)] ⋅ (rf ex) ⋅ [I (evts pre)]) /\
  (mo pre = [I (evts pre)] ⋅ (mo ex) ⋅ [I (evts pre)]) /\
  (rmw pre = [I (evts pre)] ⋅ (rmw ex) ⋅ [I (evts pre)]).

Ltac destruct_prefix H :=
  destruct H as [Hevts [Hclosed [Hsb [Hrf [Hmo Hrmw]]]]].

Ltac inverse_prefix H :=
  inversion H as [Hevts [Hclosed [Hsb [Hrf [Hmo Hrmw]]]]].

(** These lemmas allow extracting information from a prefix hypothesis without
explicitely destructing the hypothesis *)

Lemma prefix_incl_evts (pre ex: Execution):
  prefix pre ex ->
  (Included _ (evts pre) (evts ex)).
Proof. unfold prefix. intuition. Qed.

Lemma prefix_sbrf_coherence (pre ex: Execution):
  prefix pre ex ->
  forall a b, (sb ex ⊔ rf ex) a b ->
              In _ (evts pre) b ->
              In _ (evts pre) a.
Proof. unfold prefix. intuition. Qed.

(** ** Lemmas *)

(** An execution is a prefix of itself *)

Lemma prefix_itself (ex : Execution):
  valid_exec ex ->
  prefix ex ex.
Proof with auto.
  intros Hval.
  repeat (apply conj); inverse_val_exec Hval.
  - compute; auto.
  - intros a b [Hsb|Hrf] Hin.
    + apply sb_orig_evts with (y:=b); auto.
    + apply rf_orig_evts with (y:=b); auto.
  - destruct_sb_v Hsb_v.
    destruct Hsb_lso as [[Hsb_lso _] _]...
  - destruct_rf_v Hrf_v...
  - destruct_mo_v Hmo_v.
    destruct Hmopo as [? _]...
  - destruct_rmw_v Hrmw_v...
Qed.


(** The relation "being a prefix of" is transitive *)

Lemma prefix_trans (e1 e2 e3: Execution):
  prefix e1 e2 ->
  prefix e2 e3 ->
  prefix e1 e3.
Proof.
  intros Hpre1 Hpre2.
  destruct Hpre1 as [Hevts1 [Hclosed1 [Hsb1 [Hrf1 [Hmo1 Hrmw1]]]]].
  destruct Hpre2 as [Hevts2 [Hclosed2 [Hsb2 [Hrf2 [Hmo2 Hrmw2]]]]].
  repeat (apply conj).
  - intros x Hin. apply Hevts1, Hevts2 in Hin. auto.
  - intros a b Hab Hb. apply Hclosed1 with b; auto.
    apply Hevts1 in Hb.
    specialize (Hclosed2 a b Hab Hb).
    destruct Hab; [left;rewrite Hsb2|right; rewrite Hrf2]; simpl_trt; auto.
  - rewrite Hsb1. rewrite Hsb2. rewrite <-(I_simpl1 _ _ Hevts1). kat_eq.
  - rewrite Hrf1. rewrite Hrf2. rewrite <-(I_simpl1 _ _ Hevts1). kat_eq.
  - rewrite Hmo1. rewrite Hmo2. rewrite <-(I_simpl1 _ _ Hevts1). kat_eq.
  - rewrite Hrmw1. rewrite Hrmw2. rewrite <-(I_simpl1 _ _ Hevts1). kat_eq.
Qed.

(** The sequenced-before relation of an execution prefix is included in the 
sequenced-before relation of the execution *)

Lemma sb_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  sb pre ≦ sb ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  rewrite Hsb. kat.
Qed.

(** The reads-from relation of an execution prefix is included in the reads-from
relation of the execution *)

Lemma rf_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rf pre ≦ rf ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  rewrite Hrf. kat.
Qed.

(** The modification order of an execution prefix is included in the 
modification order of the execution *)

Lemma mo_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  mo pre ≦ mo ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  rewrite Hmo. kat.
Qed.

(** The read-modify-write relation of an execution prefix is included in the 
read-modify-write relation of the execution *)

Lemma rmw_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rmw pre ≦ rmw ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  rewrite Hrmw. kat.
Qed.

(** The reads-before relation of an execution prefix is included in the 
reads-before relation of the execution *)

Lemma rb_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rb pre ≦ rb ex.
Proof.
  intros Hpre.
  apply incl_dot;
  destruct_prefix Hpre;
  [ rewrite Hrf, !cnvdot, injcnv | rewrite Hmo ];
  kat.
Qed.

(** The extended communication relation of an execution prefix is included in
the extend communication relation of the execution *)

Lemma not_trans_eco_prefix_incl {pre ex: Execution}:
  prefix pre ex -> (rf pre ⊔ mo pre ⊔ rb pre) ≦ (rf ex ⊔ mo ex ⊔ rb ex).
Proof.
  intros Hpre x y [[H | H] | H].
  - left; left. apply (rf_prefix_incl Hpre). auto.
  - left; right. apply (mo_prefix_incl Hpre). auto.
  - right. apply (rb_prefix_incl Hpre). auto.
Qed.

Lemma eco_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  eco pre ≦ eco ex.
Proof.
  intros Hpre.
  apply tc_incl. apply not_trans_eco_prefix_incl.
  auto.
Qed.

(** The release-sequence relation of an execution prefix is included in the
release-sequence relation of the execution *)

Lemma maybe_rf_seq_rmw_prefix_incl {pre ex : Execution}:
  prefix pre ex ->
  (rf pre ⋅ rmw pre) ? ≦ (rf ex ⋅ rmw ex) ?.
Proof.
  intros Hpre.
  apply refl_incl. apply incl_dot.
  - apply (rf_prefix_incl Hpre).
  - apply (rmw_prefix_incl Hpre).
Qed.

Lemma rs_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rs pre ≦ rs ex.
Proof.
  intros Hpre.
  unfold rs.
  apply incl_dot.
  - do 3 (apply incl_dot; auto).
    apply refl_incl.
    apply (sb_prefix_incl Hpre).
  - apply rtc_incl.
    apply incl_dot.
    + apply (rf_prefix_incl Hpre).
    + apply (rmw_prefix_incl Hpre).
Qed.

(** The synchronises-with relation of an execution prefix is included in the
synchronises-with relation of the execution *)

Lemma sw_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  (sw pre) ≦ (sw ex).
Proof.
  intros Hpre.
  unfold sw.
  apply incl_dot; auto.
  apply incl_dot.
  do 2 (apply incl_dot; auto).
  apply incl_dot.
  apply incl_dot.
  apply incl_dot; auto.
  apply refl_incl.
  apply incl_dot; auto.
  - apply (sb_prefix_incl Hpre).
  - apply (rs_prefix_incl Hpre).
  - apply (rf_prefix_incl Hpre).
  - apply refl_incl.
    apply incl_dot; auto.
    apply (sb_prefix_incl Hpre).
Qed.

(** The happens-before relation of an execution prefix is included in the
happens-before relation of the execution *)

Lemma not_trans_hb_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  (sb pre ⊔ sw pre) ≦ (sb ex ⊔ sw ex).
Proof.
  intros Hpre. apply incl_cup.
  - apply (sb_prefix_incl Hpre).
  - apply (sw_prefix_incl Hpre).
Qed.

Lemma hb_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  (hb pre) ≦ (hb ex).
Proof.
  intros Hpre.
  unfold hb. apply tc_incl.
  apply (not_trans_hb_prefix_incl Hpre).
Qed.

(** The SC-before of an execution prefix is included in the SC-before of the 
execution *)

Lemma scb_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  (scb pre) ≦ (scb ex).
Proof.
  intros Hpre.
  apply incl_cup.
  apply incl_cup.
  apply incl_cup.
  apply incl_cup.
  apply (sb_prefix_incl Hpre).
  apply incl_dot.
  apply incl_dot.
  apply res_neq_loc_incl.
  apply (sb_prefix_incl Hpre).
  apply (hb_prefix_incl Hpre).
  apply res_neq_loc_incl.
  apply (sb_prefix_incl Hpre).
  apply res_loc_incl.
  apply (hb_prefix_incl Hpre).
  apply (mo_prefix_incl Hpre).
  apply (rb_prefix_incl Hpre).
Qed.

(** The partial SC Base relation of an execution prefix is included in the 
partial SC Base relation of the execution *)

Lemma psc_base_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  (psc_base pre) ≦ (psc_base ex).
Proof.
  intros Hpre.
  unfold psc_base.
  apply incl_dot.
  apply incl_dot.
  apply incl_cup; auto.
  apply incl_dot. auto.
  apply refl_incl.
  apply (hb_prefix_incl Hpre).
  apply (scb_prefix_incl Hpre).
  apply incl_cup; auto.
  apply incl_dot.
  apply refl_incl.
  apply (hb_prefix_incl Hpre).
  auto.
Qed.

(** The partial SC Fence relation of an execution prefix is included in the 
partial SC Fence relation of the execution *)

Lemma psc_fence_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  (psc_fence pre) ≦ (psc_fence ex).
Proof.
  intros Hpre.
  apply incl_dot; auto.
  apply incl_dot; auto.
  apply incl_dot; auto.
  apply incl_cup.
  apply (hb_prefix_incl Hpre).
  apply incl_dot.
  apply incl_dot.
  apply (hb_prefix_incl Hpre).
  apply (eco_prefix_incl Hpre).
  apply (hb_prefix_incl Hpre).
Qed.

(** The partial SC relation of an execution prefix is included in the partial SC
relation of the execution *)

Lemma psc_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  (psc pre) ≦ (psc ex).
Proof.
  intros Hpre.
  apply incl_cup.
  - apply (psc_base_prefix_incl Hpre).
  - apply (psc_fence_prefix_incl Hpre).
Qed.

(** ** Validity *)

(** If a set of events is valid, the set of events of any of its prefixes is
also a valid set of events *)

Lemma prefix_evts_valid {pre ex: Execution}:
  valid_evts (evts ex) ->
  prefix pre ex ->
  valid_evts (evts pre).
Proof.
  intros [Hevts_v1 Hevts_v2] Hpre.
  destruct Hpre as [? _]. apply conj.
  - intros e1 e2 Hin1 Hin2. auto.
  - intros e Hin. auto.
Qed.

(** If the sequenced-before relation of an execution is a linear strict order,
the sequenced-before relation of any of its prefixes is a linear strict order *)

Lemma prefix_lso_valid {pre ex: Execution}:
  linear_strict_order (sb ex) (evts ex) ->
  prefix pre ex ->
  linear_strict_order (sb pre) (evts pre).
Proof.
  intros [[Hincl [Htrans Hirr]] Htot] Hpre.
  inverse_prefix Hpre.
  repeat (apply conj).
  - rewrite Hsb. kat_eq.
  - rewrite Hsb. rewrite <- Htrans at 3. kat.
  - intros x Href. apply (Hirr x).
    apply (sb_prefix_incl Hpre) in Href. auto.
  - intros x y Hdiff Hinx Hiny.
    rewrite Hsb.
    apply Hevts in Hinx as Hinxpre.
    apply Hevts in Hiny as Hinypre.
    pose proof (Htot _ _ Hdiff Hinxpre Hinypre) as [Hsbex|Hsbex];
    [left|right]; simpl_trt; auto. 
Qed.

(** If the sequenced-before relation of an execution is valid, the
sequenced-before relation of any of its prefixes is valid *)

Lemma prefix_sb_valid {pre ex: Execution}:
  valid_sb (evts ex) (sb ex) ->
  prefix pre ex ->
  valid_sb (evts pre) (sb pre).
Proof.
  intros Hsb_v Hpre.
  inverse_prefix Hpre. destruct_sb_v Hsb_v.
  split.
  { eauto using prefix_lso_valid. }
  intros l. destruct (Hsbinit l) as [e [? [? [H H']]]]. exists e.
  splitall; auto.
  - intros Hnot. apply H.
    rewrite Hsb in Hnot.
    eapply (elt_ran_incl _ _ _ _ Hnot).
    Unshelve. kat.
  - intros e' Hinsbpre. rewrite Hsb.
    rewrite Hsb in Hinsbpre.
    simpl_trt;
    eapply ran_trt in Hinsbpre as [Hine' [y [Hine Hr]]].
    + eapply (Hclosed _ e'); eauto.
      left. eapply H'. exists y. eauto.
    + eapply H'. exists y. eauto.
    + auto.
Qed.

(** If the read-modify write relation of an execution is valid, the read-modify-
write relation of any of its prefixes is valid *)

Lemma prefix_imm_sb {pre ex: Execution} (r w: Event):
  imm (sb ex) r w ->
  prefix pre ex ->
  rmw pre r w ->
  imm (sb pre) r w.
Proof.
  intros Himm Hpre Hrmwpre.
  destruct_prefix Hpre.
  unfold imm in Himm.
  destruct Himm as [Hsbimm [H1 H2]]. split;[|split].
  - rewrite Hrmw in Hrmwpre. rewrite Hsb.
    apply simpl_trt_hyp in Hrmwpre as [? [? ?]]; 
    simpl_trt; auto.
  - intros c Hsbpre. rewrite Hsb in Hsbpre. rewrite Hrmw in Hrmwpre.
    apply simpl_trt_hyp in Hsbpre as [? [Hsbex ?]].
    apply simpl_trt_hyp in Hrmwpre as [? [Hrmwpre ?]].
    destruct (H1 c Hsbex) as [Href|Href].
    + left. rewrite Hsb; simpl_trt; auto.
    + right. auto.
  - intros c Hsbpre. rewrite Hsb in Hsbpre. rewrite Hrmw in Hrmwpre.
    apply simpl_trt_hyp in Hsbpre as [? [Hsbex ?]].
    apply simpl_trt_hyp in Hrmwpre as [? [Hrmwpre ?]].
    destruct (H2 c Hsbex) as [Href|Href].
    + left. rewrite Hsb; simpl_trt; auto.
    + right. auto.
Qed.

Lemma prefix_rmw_pair_valid {pre ex: Execution} (r w: Event):
  valid_rmw_pair (sb ex) r w ->
  prefix pre ex ->
  rmw pre r w ->
  valid_rmw_pair (sb pre) r w.
Proof.
  intros Hvalpair Hpre Hrmw.
  unfold valid_rmw_pair in *.
  destruct (get_mode r); destruct (get_mode w); auto;
  destruct Hvalpair as [Hisr [Hisw [Hgetl Himm]]];
  (split;[|split;[|split]]);
  eauto using prefix_imm_sb.
Qed.

Lemma prefix_rmw_valid {pre ex: Execution}:
  valid_rmw (evts ex) (sb ex) (rmw ex) ->
  prefix pre ex ->
  valid_rmw (evts pre) (sb pre) (rmw pre).
Proof.
  intros [Hrmwv Hudr] Hpre.
  inverse_prefix Hpre.
  split.
  - intros r w Hrmwpre.
    eapply prefix_rmw_pair_valid; eauto.
    apply Hrmwv. eapply rmw_prefix_incl; eauto.
  - rewrite Hrmw. kat_eq.
Qed.

(** If the read-modify-write relation of an execution is valid on the events
and the sequenced-before relation of the execution, the read-modify-write 
relation of the prefix of a prefix of the execution is valid on the events and
sequenced-before relation of the prefix of the execution *)

Lemma prefix_rmw_valid_diff_evts {pre1 pre2 ex: Execution}:
  valid_rmw (evts ex) (sb ex) (rmw ex) ->
  prefix pre1 pre2 ->
  prefix pre2 ex ->
  valid_rmw (evts pre2) (sb pre2) (rmw pre1).
Proof.
  intros Hval Hpre1 Hpre2.
  split.
  - intros r w Hrmwpre.
    eapply prefix_rmw_pair_valid.
    + destruct Hval as [Hval _].
      apply (rmw_prefix_incl Hpre1) in Hrmwpre.
      apply (rmw_prefix_incl Hpre2) in Hrmwpre.
      specialize (Hval r w Hrmwpre). eauto.
    + auto.
    + apply (rmw_prefix_incl Hpre1) in Hrmwpre. auto.
  - destruct_prefix Hpre1. rewrite Hrmw.
    rewrite <-(I_simpl1 _ _ Hevts). kat_eq.
Qed.

(** If the read-from relation of an execution is valid, the read-from relation
of any of its prefixes is valid *)

Lemma prefix_rf_valid {pre ex: Execution}:
  valid_rf (evts ex) (rf ex) ->
  prefix pre ex ->
  valid_rf (evts pre) (rf pre).
Proof.
  intros Hrf_v Hpre.
  inverse_prefix Hpre. destruct_rf_v Hrf_v.
  repeat (apply conj).
  - intros w r Hrfpre.
    apply (rf_prefix_incl Hpre) in Hrfpre.
    eauto using Hrfco.
  - rewrite Hrf. kat_eq.
  - rewrite Hrf. rewrite <-Hrfwr. kat_eq.
  - intros w1 w2 r [Hrfpre1 Hrfpre2].
    eapply Hrfun. split;
    eapply rf_prefix_incl; eauto.
Qed.

(** If the read-from relation of an execution is valid on the events of the
execution, the read-from relation of the prefix of the prefix of an execution is
valid on the events of the prefix of the execution *)

Lemma prefix_rf_valid_diff_evts {pre1 pre2 ex: Execution}:
  valid_rf (evts ex) (rf ex) ->
  prefix pre1 pre2 ->
  prefix pre2 ex ->
  valid_rf (evts pre2) (rf pre1).
Proof.
  intros Hrf_v Hpre1 Hpre2.
  destruct_rf_v Hrf_v.
  pose proof (prefix_trans _ _ _ Hpre1 Hpre2) as Hpre3.
  repeat (apply conj).
  - intros w r Hrf.
    eapply (rf_prefix_incl Hpre3) in Hrf.
    eauto using Hrfco.
  - destruct_prefix Hpre1. rewrite Hrf.
    rewrite <-(I_simpl1 _ _ Hevts). kat_eq.
  - destruct_prefix Hpre3. rewrite Hrf. rewrite <-Hrfwr. kat_eq.
  - intros w1 w2 r [H1 H2]. eapply Hrfun. split;
    eapply rf_prefix_incl; eauto.
Qed.

(** If the modification order of an execution is valid, the modification order
of a prefix of the execution is valid *)

Lemma prefix_mo_valid {pre ex: Execution}:
  valid_mo (evts ex) (mo ex) ->
  prefix pre ex ->
  valid_mo (evts pre) (mo pre).
Proof.
  intros Hmo_v Hpre.
  inverse_prefix Hpre. destruct_mo_v Hmo_v.
  split;[|split; [|split]].
  - rewrite Hmo, <- Hmoww. kat_eq.
  - intros x y Hmopre. rewrite Hmo in Hmopre.
    apply simpl_trt_hyp in Hmopre. eapply Hmosameloc.
    intuition eauto.
  - split;[|split]; destruct Hmopo as [_ [Hmotrans Hmoirr]].
    + rewrite Hmo. kat_eq.
    + rewrite Hmo. rewrite <- Hmotrans at 3. kat.
    + eauto using incl_irr, mo_prefix_incl.
  - intros l x y Hdiff Hin1 Hin2. rewrite Hmo.
    inversion Hin1 as [Hine1 _]. inversion Hin2 as [Hine2 _].
    apply (writes_loc_incl _ _ _ _ Hevts) in Hin1.
    apply (writes_loc_incl _ _ _ _ Hevts) in Hin2.
    destruct (Hmotot l x y Hdiff Hin1 Hin2) as [[? [? ?]]|[? [? ?]]]; [left|right];
    (split; [simpl_trt|split]; auto).
Qed.


(** If an execution is valid, any of its prefixes is also a valid execution *)

Theorem prefix_valid {pre ex: Execution}:
  valid_exec ex ->
  prefix pre ex ->
  valid_exec pre.
Proof.
  intros Hval Hpre.
  destruct_val_exec Hval.
  split;[|split;[|split;[|split]]].
  - eauto using prefix_evts_valid.
  - eauto using prefix_sb_valid.
  - eauto using prefix_rmw_valid.
  - eauto using prefix_rf_valid.
  - eauto using prefix_mo_valid.
Qed.

(** If an execution is complete, all its prefix are complete as well *)

Theorem prefix_complete {pre ex: Execution}:
  complete_exec ex ->
  prefix pre ex ->
  complete_exec pre.
Proof.
  intros [Hval Hincl] Hpre.
  split.
  - eapply prefix_valid; eauto.
  - inversion Hpre as [H _].
    intros x [Hxe Hxr].
    apply H in Hxe as H1.
    assert (In _ (reads (evts ex)) x) as H2.
    { split; auto. }
    apply Hincl in H2.
    destruct H2 as [y H2].
    exists y.
    destruct_prefix Hpre.
    rewrite Hrf.
    simpl_trt; auto. unfold I.
    eapply Hclosed. right; eauto.
    auto.
Qed.

(** The prefix of an execution that respects atomicity, respects atomicity
itself *)

Theorem prefix_atomicity {pre ex: Execution}:
  atomicity ex ->
  prefix pre ex ->
  atomicity pre.
Proof.
  intros Hat Hpre.
  intros x y Hnot. destruct Hnot as [Hrmw Hrbmo].
  apply (rmw_prefix_incl Hpre) in Hrmw.
  destruct Hrbmo as [z Hrb Hmo].
  apply (rb_prefix_incl Hpre) in Hrb.
  apply (mo_prefix_incl Hpre) in Hmo.
  assert ((rmw ex ⊓ (rb ex ⋅ mo ex)) x y) as Hcontr.
  { split. auto. exists z; auto. }
  apply Hat in Hcontr. destruct Hcontr.
Qed.

(** ** RC11-consistency *)

(** If an execution is RC11-consistent, all its prefixes are RC11-consistent *)

Theorem prefix_rc11_consistent {pre ex: Execution}:
  rc11_consistent ex ->
  prefix pre ex ->
  rc11_consistent pre.
Proof.
  intros [Hco [Hat [Hsc Hoota]]] Hpre; repeat (try split).
  (* Prefixing preserves coherence *)
  - intros x Hnot.
    destruct Hnot as [z Hnot1 Hnot2]. destruct (Hco x).
    exists z.
    + apply (hb_prefix_incl Hpre). auto.
    + apply (refl_incl _ _ (eco_prefix_incl Hpre)). auto.
  (* Prefixing preserves atomicity *)
  - eapply prefix_atomicity; eauto.
  (* Prefixing preserves the SC condition *)
  - apply (ac_incl _ _ Hsc (psc_prefix_incl Hpre)).
  (* Prefixing preserves the No-Thin-Air condition *)
  - assert (sb pre ⊔ rf pre ≦ sb ex ⊔ rf ex) as Hincl.
    + apply incl_cup.
      * apply (sb_prefix_incl Hpre).
      * apply (rf_prefix_incl Hpre).
    + apply (ac_incl _ _ Hoota Hincl).
Qed.

(** ** SC-consistency *)

Theorem prefix_sc_consistent {pre ex: Execution}:
  sc_consistent ex ->
  prefix pre ex ->
  sc_consistent pre.
Proof.
  intros [Hat Hsc] Hpre. split.
  - eapply prefix_atomicity; eauto.
  - unshelve (eapply (ac_incl _ _ Hsc _)).
    apply incl_cup.
    apply incl_cup.
    apply incl_cup.
    + eapply sb_prefix_incl; eauto.
    + eapply rf_prefix_incl; eauto.
    + eapply mo_prefix_incl; eauto.
    + eapply rb_prefix_incl; eauto.
Qed.
