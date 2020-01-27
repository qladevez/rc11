(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import rc11.

Import RelNotations.

Set Implicit Arguments.

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

Definition prefix (e' e : Execution) : Prop :=
  (Included _ e'.(evts) e.(evts)) /\
  (Same_set _ (ran e.(sb)) (ran e'.(sb))) /\
  (forall a b, (rel_union e.(sb) e.(rf)) a b ->
               In _ e'.(evts) b ->
               In _ e'.(evts) a) /\
  (same_rel e'.(sb) (res_eset e'.(evts) e.(sb))) /\
  (same_rel e'.(rf) (res_eset e'.(evts) e.(rf))) /\
  (same_rel e'.(mo) (res_eset e'.(evts) e.(mo))) /\
  (same_rel e'.(rmw) (res_eset e'.(evts) e.(rmw))).

Ltac destruct_prefix H :=
  destruct H as [Hevts [Hinit [Hclosed [Hsb [Hrf [Hmo Hrmw]]]]]].

(** If a relation [R] is included in a relation [R'], the relation [R]
restricted to pairs of events affecting the same location is included in the
relation [R'] restricted to the pairs of events affecting the same location *)

Lemma res_eq_loc_prefix_incl : forall pre ex R R',
  prefix pre ex ->
  rel_incl R' R ->
  rel_incl (res_eq_loc R') (res_eq_loc R).
Proof.
  intros pre ex R' R Hpre Hincl x y H.
  destruct H as [Hr Heq]. split; auto.
Qed.

(** If a relation [R] is included in a relation [R'], the relation [R]
restricted to pairs of events affecting different locations is included in the
relation [R'] restricted to the pairs of events affecting different locations *)

Lemma res_neq_loc_prefix_incl : forall pre ex R R',
  prefix pre ex ->
  rel_incl R' R ->
  rel_incl (res_neq_loc R') (res_neq_loc R).
Proof.
  intros pre ex R' R Hpre Hincl x y H.
  destruct H as [Hr Hdiff]. split; auto.
Qed.

(** The sequenced-before relation of an execution prefix is included in the 
sequenced-before relation of the execution *)

Lemma sb_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl pre.(sb) ex.(sb).
Proof.
  intros pre ex Hpre. destruct_prefix Hpre.
  intros x y Hsb'. apply Hsb in Hsb'. 
  destruct Hsb' as [_ [_ H]]; auto.
Qed.

(** The reads-from relation of an execution prefix is included in the reads-from
relation of the execution *)

Lemma rf_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl pre.(rf) ex.(rf).
Proof.
  intros pre ex Hpre. destruct_prefix Hpre.
  intros x y Hrf'. apply Hrf in Hrf'. 
  destruct Hrf' as [_ [_ H]]; auto.
Qed.

(** The modification order of an execution prefix is included in the 
modification order of the execution *)

Lemma mo_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl pre.(mo) ex.(mo).
Proof.
  intros pre ex Hpre. destruct_prefix Hpre.
  intros x y Hmo'. apply Hmo in Hmo'. 
  destruct Hmo' as [_ [_ H]]; auto.
Qed.

(** The read-modify-write relation of an execution prefix is included in the 
read-modify-write relation of the execution *)

Lemma rmw_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl pre.(rmw) ex.(rmw).
Proof.
  intros pre ex Hpre. destruct_prefix Hpre.
  intros x y Hrmw'. apply Hrmw in Hrmw'. 
  destruct Hrmw' as [_ [_ H]]; auto.
Qed.

(** The reads-before relation of an execution prefix is included in the 
reads-before relation of the execution *)

Lemma rb_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (rb pre) (rb ex).
Proof.
  intros pre ex Hpre x y H.
  destruct H as [z [Hinvrf Hmo']]. 
  exists z; split; destruct_prefix Hpre.
  - apply Hrf in Hinvrf. apply (res_eset_incl Hinvrf).
  - apply Hmo in Hmo'. apply (res_eset_incl Hmo').
Qed.

(** Restricting the reads-before relation is the same as applying the definition
of reads-before on reads-from and modification order restricted *)

Lemma rb_res_evts : forall pre ex,
  prefix pre ex ->
  same_rel (rb pre) (res_eset pre.(evts) (rb ex)).
Proof.
  intros pre ex Hpre. split; intros x y H.
  - repeat (try split).
    + destruct H as [z [H _]]. destruct_prefix Hpre.
      apply Hrf in H. destruct H as [_ [H _]]. auto.
    + destruct H as [z [_ H]]. destruct_prefix Hpre.
      apply Hmo in H. destruct H as [_ [H _]]. auto.
    + apply (rb_prefix_incl Hpre H).
  - destruct H as [H1 [H2 [z [Hinvrf Hmo2]]]].
    destruct_prefix Hpre. exists z; split.
    + apply Hrf; split; auto. apply Hclosed with (b := x).
      * right. apply Hinvrf.
      * auto.
    + apply Hmo; split; auto. apply Hclosed with (b := x).
      * right. apply Hinvrf.
      * auto.
Qed.

(** The extended communication relation of an execution prefix is included in
the extend communication relation of the execution *)

Lemma not_trans_eco_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (rel_union pre.(rf) (rel_union pre.(mo) (rb pre)))
           (rel_union ex.(rf) (rel_union ex.(mo) (rb ex))).
Proof.
  intros pre ex Hpre x y [H | [H | H]].
  - left. apply (rf_prefix_incl Hpre). auto.
  - right; left. apply (mo_prefix_incl Hpre). auto.
  - right; right. apply (rb_prefix_incl Hpre). auto.
Qed.

Lemma eco_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (eco pre) (eco ex).
Proof.
  intros pre ex Hpre.
  apply tc_incl. apply not_trans_eco_prefix_incl.
  auto.
Qed.

(** The release-sequence relation of an execution prefix is included in the
release-sequence relation of the execution *)

Lemma maybe_rf_seq_rmw_prefix_incl: forall pre ex,
  prefix pre ex ->
  rel_incl ((pre.(rf) ;; pre.(rmw)) ?) ((ex.(rf) ;; ex.(rmw)) ?).
Proof.
  intros pre ex Hpre x y H.
  destruct H as [H | H].
  - left. destruct H as [z [H1 H2]]; exists z; split.
    + apply (rf_prefix_incl Hpre). auto.
    + apply (rmw_prefix_incl Hpre). auto.
  - right. auto.
Qed.

Lemma rs_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (rs pre) (rs ex).
Proof.
  intros pre ex Hpre x y H.
  destruct H as [z1 [Hw H]]. exists z1; split. auto.
  destruct H as [z2 [Hreseqloc H]]. exists z2; split.
  { destruct Hreseqloc as [Hreseqloc | Hreseqloc].
    - left. destruct Hreseqloc as [Hsb' Heq]; split; auto.
      apply (sb_prefix_incl Hpre). auto.
    - right. auto.
  }
  destruct H as [z3 [Hwrlx H]]. exists z3; split. auto.
  apply maybe_rf_seq_rmw_prefix_incl in Hpre as H'.
  apply tc_incl in H'. apply H' in H. auto.
Qed.

  
(** The synchronises-with relation of an execution prefix is included in the
synchronises-with relation of the execution *)

Lemma sw_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (sw pre) (sw ex).
Proof.
  intros pre ex Hpre x y H.
  destruct H as [z1 [Heseqmode H]]. exists z1; split. auto.
  destruct H as [z2 [Hforigin H]]. exists z2; split.
  { destruct Hforigin as [Hforigin | Hforigin].
    - left. destruct Hforigin as [z2' [H1 H2]]. exists z2'; split. auto.
      apply (sb_prefix_incl Hpre). auto.
    - right. auto.
  }
  destruct H as [z3 [Hrs H]]. exists z3; split.
  { apply (rs_prefix_incl Hpre) in Hrs. auto. }
  destruct H as [z4 [Hrf H]]. exists z4; split.
  { apply (rf_prefix_incl Hpre) in Hrf. auto. }
  destruct H as [z5 [Hrseqmode H]]. exists z5; split. auto.
  destruct H as [z6 [Hfdest H]]. exists z6; split.
  { destruct Hfdest as [Hfdest | Hfdest].
    - left. destruct Hfdest as [z6' [H1 H2]]. exists z6'; split.
      + apply (sb_prefix_incl Hpre). auto.
      + auto.
    - right. auto.
  }
  auto.
Qed.

(** The happens-before relation of an execution prefix is included in the
happens-before relation of the execution *)

Lemma not_trans_hb_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (pre.(sb) ;; (sw pre)) (ex.(sb) ;; (sw ex)).
Proof.
  intros pre ex Hpre x y [z [H1 H2]]; exists z; split.
  - apply (sb_prefix_incl Hpre). auto.
  - apply (sw_prefix_incl Hpre). auto.
Qed.

Lemma hb_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (hb pre) (hb ex).
Proof.
  intros pre ex Hpre.
  apply not_trans_hb_prefix_incl in Hpre as H.
  apply (tc_incl H).
Qed.

(** The SC-before of an execution prefix is included in the SC-before of the 
execution *)

Lemma scb_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (scb pre) (scb ex).
Proof.
  intros pre ex Hpre x y H.
  destruct H as [H | H].
  { left. apply (sb_prefix_incl Hpre). auto. }
  destruct H as [H | H].
  { right. left. destruct H as [z [H1 H]]. exists z; split.
    { apply (res_neq_loc_prefix_incl Hpre (sb_prefix_incl Hpre)). auto. }
    destruct H as [z1 [H2 H]]. exists z1; split.
    - apply (hb_prefix_incl Hpre). auto.
    - apply (res_neq_loc_prefix_incl Hpre (sb_prefix_incl Hpre)). auto. }
  right; right. destruct H as [H | H].
  { left. apply (res_eq_loc_prefix_incl Hpre (hb_prefix_incl Hpre)). auto. }
  right. destruct H as [H | H].
  - left. apply (mo_prefix_incl Hpre). auto.
  - right. apply (rb_prefix_incl Hpre). auto.
Qed.

(** The partial SC Base relation of an execution prefix is included in the 
partial SC Base relation of the execution *)

Lemma psc_base_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (psc_base pre) (psc_base ex).
Proof.
  intros pre ex Hpre x y H.
  destruct H as [z1 [Hscorhbfence H]]. exists z1; split.
  { destruct Hscorhbfence as [Hsc | Hhbfence].
    - left. auto.
    - right. destruct Hhbfence as [z [Hf Hhb]]. exists z; split.
      + auto.
      + destruct Hhb as [Hhb | Href].
        * left. apply (hb_prefix_incl Hpre). auto.
        * right. auto.
  }
  destruct H as [z2 [Hscb H]]. exists z2; split.
  { apply (scb_prefix_incl Hpre). auto. }
  destruct H as [H | H].
  { left. auto. }
  destruct H as [z3 [Hhb Hf]]. right; exists z3; split.
  - destruct Hhb.
    + left. apply (hb_prefix_incl Hpre). auto.
    + right. auto.
  - auto.
Qed.

(** The partial SC Fence relation of an execution prefix is included in the 
partial SC Fence relation of the execution *)

Lemma psc_fence_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (psc_fence pre) (psc_fence ex).
Proof.
  intros pre ex Hpre x y H.
  destruct H as [z [Hfbegin H]]. exists z; split.
  { auto. }
  destruct H as [z1 [H Hfend]]. exists z1; split.
  - destruct H as [H | H].
    { left. apply (hb_prefix_incl Hpre). auto. }
    { right. destruct H as [z2 [Hhb H]]. exists z2; split.
      { apply (hb_prefix_incl Hpre). auto. }
      destruct H as [z3 [Heco Hhb']]. exists z3; split.
      - apply (eco_prefix_incl Hpre). auto.
      - apply (hb_prefix_incl Hpre). auto. }
  - auto.
Qed.

(** The partial SC relation of an execution prefix is included in the partial SC
relation of the execution *)

Lemma psc_prefix_incl : forall pre ex,
  prefix pre ex ->
  rel_incl (psc pre) (psc ex).
Proof.
  intros pre ex Hpre x y [Hpsc | Hpsc].
  - left. apply (psc_base_prefix_incl Hpre). auto.
  - right. apply (psc_fence_prefix_incl Hpre). auto.
Qed.

(** ** RC11-consistency *)

(** If an execution is RC11-consistent, all its prefixes are RC11-consistent *)

Lemma prefix_rc11_consistent:
  forall pre ex,
    rc11_consistent ex ->
    prefix pre ex ->
    rc11_consistent pre.
Proof.
  intros pre ex [Hco [Hat [Hsc Hoota]]] Hpre; repeat (try split).
  (* Prefixing preserves coherence *)
  - intros x Hnot.
    destruct Hnot as [z [Hnot1 Hnot2]]. destruct (Hco x).
    exists z; split.
    + apply (hb_prefix_incl Hpre). auto.
    + destruct Hnot2 as [Hnot2 | Hnot2].
      * left. apply (eco_prefix_incl Hpre). auto.
      * right. auto.
  (* Prefixing preserves atomicity *)
  - intros x y Hnot. destruct Hnot as [Hrmw Hrbmo].
    apply (rmw_prefix_incl Hpre) in Hrmw.
    destruct Hrbmo as [z [Hrb Hmo]].
    apply (rb_prefix_incl Hpre) in Hrb.
    apply (mo_prefix_incl Hpre) in Hmo.
    assert ((rel_inter (rmw ex) ((rb ex) ;; (mo ex))) x y) as Hcontr.
    { split. auto. exists z; auto. }
    apply Hat in Hcontr. destruct Hcontr.
  (* Prefixing preserves the SC condition *)
  - apply (ac_incl Hsc (psc_prefix_incl Hpre)).
  (* Prefixing preserves the No-Thin-Air condition *)
  - assert (rel_incl (rel_union (sb pre) (rf pre)) (rel_union (sb ex) (rf ex))) as Hincl.
    + intros x y H. destruct H as [H | H].
      * left. apply (sb_prefix_incl Hpre). auto.
      * right. apply (rf_prefix_incl Hpre). auto.
    + apply (ac_incl Hoota Hincl).
Qed.
