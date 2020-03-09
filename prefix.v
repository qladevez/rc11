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

Definition prefix (e' e : Execution) : Prop :=
  (Included _ (evts e') (evts e)) /\
  (forall a b, (sb e ⊔ rf e) a b ->
               In _ (evts e') b ->
               In _ (evts e') a) /\
  (sb e' ≡ sb e) /\
  (rf e' ≡ rf e) /\
  (mo e' ≡ mo e) /\
  (rmw e' ≡ rmw e).

Ltac destruct_prefix H :=
  destruct H as [Hevts [Hclosed [Hsb [Hrf [Hmo Hrmw]]]]].

(** ** Lemmas *)

(** An execution is a prefix of itself *)

Lemma prefix_itself (ex : Execution):
  valid_exec ex ->
  prefix ex ex.
Proof.
  intros Hval.
  split; [|split; [|split; [|split; [|split]]]].
  - compute; auto.
  - intros a b [Hsb|Hrf] Hin.
    + apply sb_orig_evts with (y:=b); auto.
    + apply rf_orig_evts with (y:=b); auto.
  - compute; auto.
  - compute; auto.
  - compute; auto.
  - compute; auto.
Qed.

(** If a relation [R] is included in a relation [R'], the relation [R]
restricted to pairs of events affecting the same location is included in the
relation [R'] restricted to the pairs of events affecting the same location *)

Lemma res_eq_loc_prefix_incl : forall pre ex R R',
  prefix pre ex ->
  R' ≦ R ->
  res_eq_loc R' ≦ res_eq_loc R.
Proof.
  intros pre ex R' R Hpre Hincl x y H.
  destruct H as [Hr Heq]. split; auto.
  apply Hincl. auto.
Qed.

(** If a relation [R] is included in a relation [R'], the relation [R]
restricted to pairs of events affecting different locations is included in the
relation [R'] restricted to the pairs of events affecting different locations *)

Lemma res_neq_loc_prefix_incl : forall pre ex R R',
  prefix pre ex ->
  R' ≦ R ->
  res_neq_loc R' ≦ res_neq_loc R.
Proof.
  intros pre ex R' R Hpre Hincl x y H.
  destruct H as [Hr Hdiff]. split; auto.
  apply Hincl. auto.
Qed.

(** The sequenced-before relation of an execution prefix is included in the 
sequenced-before relation of the execution *)

Lemma sb_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  sb pre ≦ sb ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  intros x y Hsb'. apply Hsb in Hsb'.
  auto.
Qed.

(** The reads-from relation of an execution prefix is included in the reads-from
relation of the execution *)

Lemma rf_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rf pre ≦ rf ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  intros x y Hrf'. apply Hrf in Hrf'. 
  auto.
Qed.

(** The modification order of an execution prefix is included in the 
modification order of the execution *)

Lemma mo_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  mo pre ≦ mo ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  intros x y Hmo'. apply Hmo in Hmo'. 
  auto.
Qed.

(** The read-modify-write relation of an execution prefix is included in the 
read-modify-write relation of the execution *)

Lemma rmw_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rmw pre ≦ rmw ex.
Proof.
  intros Hpre. destruct_prefix Hpre.
  intros x y Hrmw'. apply Hrmw in Hrmw'.
  auto.
Qed.

(** The reads-before relation of an execution prefix is included in the 
reads-before relation of the execution *)

Lemma rb_prefix_incl {pre ex: Execution}:
  prefix pre ex ->
  rb pre ≦ rb ex.
Proof.
  intros Hpre x y H.
  destruct H as [z Hinvrf Hmo'].
  exists z; destruct_prefix Hpre.
  - apply Hrf in Hinvrf. unfold transp. auto.
  - apply Hmo in Hmo'. auto.
Qed.

(** Restricting the reads-before relation is the same as applying the definition
of reads-before on reads-from and modification order restricted *)

Lemma rb_res_evts {pre ex: Execution}:
  prefix pre ex ->
  rb pre ≡ rb ex.
Proof.
  intros Hpre. apply antisym; intros x y H.
  - apply (rb_prefix_incl Hpre _ _ H).
  - destruct H as [z H1 H2].
    destruct_prefix Hpre. exists z.
    + apply Hrf; auto.
    + apply Hmo; auto.
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
  unfold scb.
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
  unfold psc_fence.
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
  unfold psc.
  apply incl_cup.
  - apply (psc_base_prefix_incl Hpre).
  - apply (psc_fence_prefix_incl Hpre).
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