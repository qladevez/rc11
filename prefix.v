(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.
Require Import Ensembles.
Require Import Relations.
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
  (sb pre = res_eset (evts pre) (sb ex)) /\
  (rf pre = res_eset (evts pre) (rf ex)) /\
  (mo pre = res_eset (evts pre) (mo ex)) /\
  (rmw pre = res_eset (evts pre) (rmw ex)).

Ltac destruct_prefix H :=
  destruct H as [Hevts [Hclosed [Hsb [Hrf [Hmo Hrmw]]]]].

Ltac inverse_prefix H :=
  inversion H as [Hevts [Hclosed [Hsb [Hrf [Hmo Hrmw]]]]].

(** These lemmas allow extracting information from a prefix hypothesis without
explicitely destructing the hypothesis, which is more robust *)

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
Proof.
  intros Hval.
  splitall.
  - compute; auto.
  - intros a b [Hsb|Hrf] Hin.
    + apply sb_orig_evts with (y:=b); auto.
    + apply rf_orig_evts with (y:=b); auto.
  - destruct_val_exec Hval. destruct_sb_v Hsb_v.
    auto using res_eset_udr.
  - destruct_val_exec Hval. destruct_rf_v Hrf_v.
    auto using res_eset_udr.
  - destruct_val_exec Hval. destruct_mo_v Hmo_v.
    destruct Hmopo as [? _].
    auto using res_eset_udr.
  - destruct_val_exec Hval. destruct_rmw_v Hrmw_v.
    auto using res_eset_udr.
Qed.

(** The sequenced-before relation of an execution prefix is included in the 
sequenced-before relation of the execution *)

Lemma sb_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  sb pre ≦ sb ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  rewrite Hsb. apply res_eset_incl.
Qed.

(** The reads-from relation of an execution prefix is included in the reads-from
relation of the execution *)

Lemma rf_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rf pre ≦ rf ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  rewrite Hrf. apply res_eset_incl.
Qed.

(** The modification order of an execution prefix is included in the 
modification order of the execution *)

Lemma mo_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  mo pre ≦ mo ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  rewrite Hmo. apply res_eset_incl.
Qed.

(** The read-modify-write relation of an execution prefix is included in the 
read-modify-write relation of the execution *)

Lemma rmw_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rmw pre ≦ rmw ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  rewrite Hrmw. apply res_eset_incl.
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
  [rewrite Hrf, res_eset_cnv | rewrite Hmo];
  apply res_eset_incl.
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
  intros Hevts_v Hpre e Hin.
  destruct Hpre as [? _].
  auto.
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
  splitall.
  - intros x [y Hudr | y Hudr];
    (rewrite Hsb in Hudr; destruct Hudr as [? [? [? ?]]]; auto).
  - pose proof (sb_prefix_incl Hpre) as Hpreinc.
    intros x y [z Hfst Hsnd]. rewrite Hsb. split;[|split].
    + rewrite Hsb in Hfst. destruct Hfst. auto.
    + rewrite Hsb in Hsnd. destruct Hsnd as [? [? ?]]. auto.
    + apply Hpreinc in Hfst. apply Hpreinc in Hsnd.
      apply Htrans. exists z; auto.
  - intros x Href. apply (Hirr x).
    apply (sb_prefix_incl Hpre) in Href. auto.
  - intros x y Hdiff Hinx Hiny.
    destruct Hpre as [Hinc _].
    rewrite Hsb. apply Hinc in Hinx as Hinxpre. apply Hinc in Hiny as Hinypre.
    pose proof (Htot _ _ Hdiff Hinxpre Hinypre) as [Hsbex|Hsbex];
    [left|right]; splitall; auto.
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
  split.
  { rewrite Hsb. apply res_eset_udr_incl. }
  - intros l. destruct (Hsbinit l) as [e [? [? [H H']]]]. exists e.
    splitall; auto.
    + intros Hnot. apply H.
      rewrite Hsb in Hnot.
      destruct Hnot as [z [? [? ?]]].
      exists z. auto.
    + intros e' Hinsbpre. rewrite Hsb.
      rewrite Hsb in Hinsbpre.
      split;[|split].
      * eapply Hclosed.
        -- left. eapply H'. destruct Hinsbpre as [z [? [? ?]]].
           exists z. eauto.
        -- destruct Hinsbpre as [? [? [? ?]]]. auto.
      * destruct Hinsbpre as [? [? [? ?]]]. auto.
      * apply H'. destruct Hinsbpre as [? [? [? ?]]].
        exists x. auto.
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
  destruct Himm as [Hsbimm H]. split.
  - rewrite Hrmw in Hrmwpre. rewrite Hsb.
    destruct Hrmwpre as [? [? _]].
    splitall; auto.
  - intros c Hsbpre.
    rewrite Hsb in Hsbpre. destruct Hsbpre as [? [? Hsbex]].
    destruct (H c Hsbex) as [Href H']. split.
    + destruct Href.
      * left. rewrite Hsb. splitall; auto.
        rewrite Hrmw in Hrmwpre. destruct Hrmwpre as [? [? _]]; auto.
      * right. auto.
    + intros c' H''. rewrite Hsb in H''. destruct H'' as [_ [? H''']].
      pose proof (H' c' H''') as [Hsbrc | Href'].
      * left. rewrite Hsb. splitall; auto.
      * right. auto.
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
    apply Hrmwv. rewrite Hrmw in Hrmwpre. destruct Hrmwpre as [_ [_ ?]]. auto.
  - rewrite Hrmw.
    apply res_eset_udr_incl.
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
  split.
  - splitall; rewrite Hrf in *.
    + eauto using res_eset_elt_left.
    + eauto using res_eset_elt_right.
    + eapply Hrfco, res_eset_incl. eauto.
    + eapply Hrfco, res_eset_incl. eauto.
  - split;[|split].
    + rewrite Hrf. apply res_eset_udr_incl.
    + rewrite Hrf, test_res_eset_swap, Hrfwr. auto.
    + intros w1 w2 x [H1 H2]. rewrite Hrf in H1, H2.
      apply res_eset_incl in H1.
      apply res_eset_incl in H2.
      intuition (eauto using Hrfun).
Qed.

Lemma prefix_mo_valid {pre ex: Execution}:
  valid_mo (evts ex) (mo ex) ->
  prefix pre ex ->
  valid_mo (evts pre) (mo pre).
Proof.
  intros Hmo_v Hpre.
  inverse_prefix Hpre. destruct_mo_v Hmo_v.
  split;[|split].
  - rewrite Hmo, test_res_eset_swap, Hmoww. auto.
  - split;[|split]; destruct Hmopo as [_ [Hmotrans Hmoirr]].
    + rewrite Hmo. apply res_eset_udr_incl.
    + rewrite Hmo, res_eset_dot. auto using res_eset_prop_incl.
    + eauto using incl_irr, mo_prefix_incl.
  - intros l x y Hdiff Hin1 Hin2. rewrite Hmo.
    apply Hevts in Hin1 as Hinpre1. apply Hevts in Hin2 as Hinpre2.
    destruct (Hmotot l x y Hdiff Hinpre1 Hinpre2) as [[? [? ?]]|[? [? ?]]] ;[left|right];
    (split;[split;[|split] |split]; auto).
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
  - intros x y Hnot. destruct Hnot as [Hrmw Hrbmo].
    apply (rmw_prefix_incl Hpre) in Hrmw.
    destruct Hrbmo as [z Hrb Hmo].
    apply (rb_prefix_incl Hpre) in Hrb.
    apply (mo_prefix_incl Hpre) in Hmo.
    assert ((rmw ex ⊓ (rb ex ⋅ mo ex)) x y) as Hcontr.
    { split. auto. exists z; auto. }
    apply Hat in Hcontr. destruct Hcontr.
  (* Prefixing preserves the SC condition *)
  - apply (ac_incl _ _ Hsc (psc_prefix_incl Hpre)).
  (* Prefixing preserves the No-Thin-Air condition *)
  - assert (sb pre ⊔ rf pre ≦ sb ex ⊔ rf ex) as Hincl.
    + apply incl_cup.
      * apply (sb_prefix_incl Hpre).
      * apply (rf_prefix_incl Hpre).
    + apply (ac_incl _ _ Hoota Hincl).
Qed.