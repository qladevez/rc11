(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import rel prop monoid kat relalg kat_tac.
From RC11 Require Import proprel_classic.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import rc11.
From RC11 Require Import prefix.
From RC11 Require Import conflict.
From RC11 Require Import numbering.
Require Import Lia.
Require Import Ensembles.
Require Import Relations.
Require Import Classical_Prop.

Open Scope rel_notations.

(** This file contains the proof of the DRF property, i.e. Theorem 4 of Section
8 of the article, that we copy here:

Theorem 4. If in all SC-consistent executions of a program P , every race 〈a, b〉
has mod(a) = mod(b) = sc, then the outcomes of P under RC11 coincide with those 
under SC.

Several things are important to note to understand what this theorem states
exactly:

- The set of executions of a program P is taken to be prefix-closed: a prefix of
an execution of P (which includes at least the initialisation events) is an
execution of P. (Towards the end of section 3.1)
- Definition 2: Two events a and b are called conflicting in an execution G if 
〈a, b〉 ∈ E, W ∈ {typ(a), typ(b)}, a != b, and loc(a) = loc(b). A pair〈a, b〉is 
called a race in G (denoted 〈a, b〉 ∈ race) if a and b are conflicting events in 
G, and 〈a, b〉doesn't belong to hb ∪ hb−1. *)

Definition race (ex: Execution) : rlt Event :=
  fun x => fun y => 
    (is_write x \/ is_write y) /\
    x <> y /\
    get_loc x = get_loc y /\
    ~((hb ex) x y) /\
    ~((hb ex) y x).

Module DRF (Numbering: Numbering).

Import Numbering.
Module NP := NumberingPrefix Numbering.
Import NP.

(** If a bound gives the minimal conflicting pair of an execution, it is greater
than 0 *)

Lemma mcp_bound_gt_zero (ex: Execution) (bound: nat) (k j: Event):
  minimal_conflicting_pair ex bound k j ->
  bound > 0.
Proof.
  intros Hmcp.
  apply mcp_in_evts_left in Hmcp as Hinl.
  apply mcp_in_evts_right in Hmcp as Hinr.
  destruct Hinl as [z Hevts Hord].
  destruct Hinr as [z' Hevts' Hord'].
  unfold In in Hord, Hord'.
  apply mcp_diff in Hmcp.
  rewrite (numbering_injective ex) in Hmcp.
  lia.
Qed.

(** If a bound gives the minimal conflicting pair of an execution, we can
substract one to the bound and obtain a smaller bound *)

Lemma mcp_bound_min_one_lt_bound (ex: Execution) (bound: nat) (k j: Event):
  minimal_conflicting_pair ex bound k j ->
  bound - 1 < bound.
Proof.
  intros Hmcp.
  assert (bound > 0). eauto using mcp_bound_gt_zero.
  lia.
Qed.

(** If two events are sequenced in an execution, and if the latest event's
numbering is smaller than a bound, they are still sequenced in the bounding
of the execution by the bound *)

Lemma sb_bounded (ex: Execution) (b: nat) (x y: Event):
  valid_exec ex ->
  (sb ex) x y ->
  (numbering ex y) <= b ->
  (sb (bounded_exec ex b)) x y.
Proof.
  intros Hval Hsb Hord. rew bounded.
  exists y. exists x; auto.
  - split; auto.
    apply sb_num_ord in Hsb.
    unfold NLE. lia.
  - split; auto.
Qed.

(** If a read reads it value from a write, and if the write's
numbering is smaller than a bound, the read still reads its value from its
write in the bounding of the execution by the bound *)

Lemma rf_bounded (ex: Execution) (b: nat) (x y: Event):
  valid_exec ex ->
  (rf ex) x y ->
  (numbering ex y) <= b ->
  (rf (bounded_exec ex b)) x y.
Proof.
  intros Hval Hrf Hord. rew bounded.
  exists y. exists x; auto.
  - split; auto.
    apply rf_num_ord in Hrf.
    unfold NLE. lia.
  - split; auto.
Qed.

(** If two events [x] and [y] are related by the transitive closure of the union of 
sequenced-before and read-from, and if the numbering of [y] is inferior to a
a bound, then the two events are still related by the same relation in the
bounding of the execution by the bound *)

Lemma sbrf_boundable' (ex: Execution) (b: nat):
  valid_exec ex ->
  forall (x y: Event),
  (sb ex ⊔ rf ex)^+ x y ->
  (fun j k => b >= (numbering ex y) ->
              (sb (bounded_exec ex b) ⊔ rf (bounded_exec ex b))^+ x y) x y.
Proof.
  intros Hval.
  apply tc_ind.
  - intros x y Hsbrf Hord. apply tc_incl_itself.
    destruct Hsbrf as [Hsb|Hrf].
    + left. eauto using sb_bounded.
    + right. eauto using rf_bounded.
  - intros x y z Hrxy IHrxy Hryz IHryz Hord.
    apply tc_trans with y.
    + apply IHrxy.
      apply numbering_coherent_tc in Hryz. lia.
    + apply IHryz. auto.
Qed.

Lemma sbrf_boundable (ex: Execution) (b: nat):
  valid_exec ex ->
  forall (x y: Event),
  (sb ex ⊔ rf ex)^+ x y ->
  b >= (numbering ex y) ->
  (sb (bounded_exec ex b) ⊔ rf (bounded_exec ex b))^+ x y.
Proof. apply sbrf_boundable'. Qed.

(** In a valid and rc11-consistent execution with a miniaml conflicting pair, 
any event sequenced before the biggest event of the conflicting pair, is not
related to the smallest event of the conflicting pair by the transitive closure
of the union of sequence-before and reads-from *)

Lemma sbbefore_lemma (ex: Execution) (bound: nat) (x y b: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex y) > (numbering ex x) ->
  (sb ex) b y ->
  ~((sb ex ⊔ rf ex)^+ x b).
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hsb.
  inversion Hcomp as [Hval _].
  eapply mcp_not_sbrfsc in Hmcp as Hnotsbrfsc.
  intros Hnot; apply Hnotsbrfsc.
  apply tc_trans with b.
  - assert (bound >= numbering ex b) as Hordbndb.
    { transitivity (numbering ex y).
      - eauto using mcp_right_le_bound.
      - enough (numbering ex y > numbering ex b). lia. eauto using sb_num_ord. }
    eapply sbrfsc_pre_inc.
    { apply two_ord_bounds_pre. eauto.
      eapply mcp_bound_min_one_lt_bound. eauto. }
    apply sbrf_incl_sbrfsc.
    + eapply prefix_complete; eauto.
      eapply bounded_exec_is_prefix; eauto.
    + eapply prefix_rc11_consistent; eauto.
      eapply bounded_exec_is_prefix; eauto.
    + eapply smaller_than_smallest_not_conflicting.
      * destruct Hmcp as [? _]. eauto.
      * eapply mcp_bound_min_one_lt_bound. eauto.
    + eapply sbrf_boundable; eauto.
      eapply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp.
      rewrite (max_rewrite _ _ Hord) in Hmcp.
      rewrite Hmcp in Hord. apply sb_num_ord in Hsb. lia.
  - apply tc_incl_itself. left. rew bounded.
    exists y. exists b.
    + split; auto. apply sb_num_ord in Hsb. unfold NLE.
      apply mcp_right_le_bound in Hmcp. lia.
    + auto.
    + split; auto. apply mcp_right_le_bound in Hmcp. unfold NLE. lia.
Qed.

(** In an execution with a minimal conflicting pair, no event can be sequenced
after the event of the conflicting pair with the biggest numbering *)

Lemma mcp_sb_last (ex: Execution) (bound:nat) (x y: Event):
  valid_exec ex ->
  minimal_conflicting_pair ex bound x y ->
  numbering ex x > numbering ex y ->
  (forall z, ~(sb (bounded_exec ex bound) x z)).
Proof.
  intros Hval Hmcp Hord z Hsb.
  rew bounded in Hsb.
  apply simpl_trt_hyp in Hsb as [_ [Hsb Htz]].
  apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp.
  rewrite (max_rewrite' _ _ Hord) in Hmcp.
  apply sb_num_ord in Hsb. rewrite Hmcp in Hsb.
  unfold NLE in Htz. lia.
Qed.

(** In an execution with a minimal conflicting pair, the event of the 
conflicting pair with the biggest numbering cannot reads its value from 
another event *)

Lemma mcp_rf_last (ex: Execution) (bound:nat) (x y: Event):
  valid_exec ex ->
  minimal_conflicting_pair ex bound x y ->
  numbering ex x > numbering ex y ->
  (forall z, ~(rf (bounded_exec ex bound) x z)).
Proof.
  intros Hval Hmcp Hord z Hsb.
  rew bounded in Hsb.
  apply simpl_trt_hyp in Hsb as [_ [Hsb Htz]].
  apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp.
  rewrite (max_rewrite' _ _ Hord) in Hmcp.
  apply rf_num_ord in Hsb. rewrite Hmcp in Hsb.
  unfold NLE in Htz. lia.
Qed.

(** If the event of a minimal conflicting pair with the biggest numbering is a
write, the conflicting pair cannot be related by the union of sequenced-before
and reads-from *)

Lemma mcp_write_not_sbrf (ex: Execution) (bound: nat) (x y: Event):
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) > (numbering ex y) ->
  is_write x ->
  ~((sb (bounded_exec ex bound) ⊔ rf (bounded_exec ex bound)) y x).
Proof.
  intros Hval Hrc11 Hmcp Hord Hw [Hsb|Hsw].
  - eapply mcp_not_cnv_sbrfsc. eauto. eapply tc_incl_itself. left. eauto.
  - apply rf_dest_read in Hsw.
    + destruct x; auto.
    + eapply bounded_is_valid. eauto.
Qed.

(** In a valid, rc11-consistent execution with a minimal conflicting pair, if
the event of the conflicting pair with the biggest numbering is a write event,
the two events form a race in the execution (bounded with the bound of the
minimal conflicting pair *)

Lemma mcp_write_race (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) > (numbering ex y) ->
  is_write x ->
  race (bounded_exec ex bound) x y.
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hw.
  inversion Hcomp as [Hval _].
  repeat (apply conj).
  - eauto using mcp_one_is_write.
  - eauto using mcp_diff.
  - eauto using mcp_same_loc.
  - intros Hnot. unfold hb in Hnot.
    rewrite tc_inv_dcmp2 in Hnot.
    destruct Hnot as [z [Hsb|Hsw] _].
    { eapply mcp_sb_last; eauto. }
    unfold sw in Hsw.
    apply simpl_rt_hyp in Hsw as [Hsw _].
    destruct Hsw as [w1 Hsw _].
    apply simpl_rt_hyp in Hsw as [Hsw _].
    apply simpl_rt_hyp in Hsw as [Hsw _].
    destruct Hsw as [w2 Hsw Hrf].
    destruct Hsw as [w3 Hsw Hrs].
    destruct Hsw as [w4 [Heq _] [[w5 [Heq2 _] Hsb] |Href]].
    { rewrite <- Heq in Heq2. rewrite <- Heq2 in Hsb. 
      eapply mcp_sb_last; eauto. }
    simpl in Href. rewrite <- Heq in Href. rewrite <- Href in Hrs.
    destruct Hrs as [w5 Hrs Hrfrmw].
    apply simpl_rt_hyp in Hrs as [Hrs _].
    apply simpl_trt_hyp in Hrs as [_ [Hsb _]].
    destruct Hsb as [Hsb|Href2].
    { eapply mcp_sb_last; eauto. }
    rewrite refl_trans_refl_union_trans in Hrfrmw.
    destruct Hrfrmw as [Href3 | Hrfrmw].
    { simpl in Href2, Href3. rewrite <- Href2 in Href3. rewrite <- Href3 in Hrf.
      eapply mcp_rf_last; eauto. }
    rewrite tc_inv_dcmp2 in Hrfrmw.
    destruct Hrfrmw as [w6 [w7 Hrf2 _] _].
    simpl in Href2. rewrite <- Href2 in Hrf2.
    eapply mcp_rf_last; eauto.
  - intros Hnot.
    apply hb_incl_sbrf in Hnot.
    unfold hb in Hnot. rewrite tc_inv_dcmp4 in Hnot. 
    destruct Hnot as [Hnot|Hnot].
    { eapply (mcp_write_not_sbrf ex bound x y); eauto. }
    destruct Hnot as [z Hhb Hsbsw].
    destruct Hsbsw as [Hsb|Hsw].
    + eapply (sbbefore_lemma (bounded_exec ex bound) bound y x z).
      * apply bounded_is_complete; auto.
      * apply bounded_is_rc11; auto.
      * apply mcp_bounded; auto.
        apply mcp_is_sym. auto.
      * erewrite <- (numbering_pre_stable _ _ _ x) in Hord.
        erewrite <- (numbering_pre_stable _ _ _ y) in Hord.
        Unshelve. eauto.
        all: apply bounded_exec_is_prefix; auto.
      * auto.
      * auto.
    + apply rf_dest_read in Hsw. destruct x; auto.
      apply bounded_is_valid; auto.
    + apply bounded_is_complete. auto.
Qed.

(** Under the hypothesis that every race in every SC-consistent execution of a 
program is between two SC events, then the minimal conflicting execution where
the conflicting event with the highest numbering is a write event is not
SC-consistent *)

Lemma mcp_write_not_sc (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) > (numbering ex y) ->
  is_write x ->
  (forall pre, prefix pre ex ->
               forall j k, race pre j k ->
                           ((get_mode j) = Sc /\ (get_mode k) = Sc)) ->
  ~(sc_consistent (bounded_exec ex bound)).
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hwx Hrace_not_sc Hnot.
  inversion Hcomp as [Hval _].
  apply (mcp_at_least_one_not_sc ex x y bound Hmcp).
  apply (Hrace_not_sc (bounded_exec ex bound)).
  - eapply bounded_exec_is_prefix. eauto.
  - apply mcp_write_race; auto.
Qed.

Lemma be_decomposable (ex: Execution) (bound: nat):
  valid_exec ex ->
  bound > 0 ->
  sb (bounded_exec ex bound) ⊔
  rf (bounded_exec ex bound) ⊔
  mo (bounded_exec ex bound) ⊔
  rb (bounded_exec ex bound) =
  (sb (bounded_exec ex (bound - 1)) ⊔
   rf (bounded_exec ex (bound - 1)) ⊔
   mo (bounded_exec ex (bound - 1)) ⊔
   rb (bounded_exec ex (bound - 1))) ⊔
  (sb (bounded_exec ex bound) ⊔
   rf (bounded_exec ex bound) ⊔
   mo (bounded_exec ex bound) ⊔
   rb (bounded_exec ex bound)).
Proof.
  intros Hval Hbndnotnull.
  rew bounded. apply ext_rel, antisym.
  - kat.
  - rewrite NLE_bound_min_one.
    assert (prefix (bounded_exec ex (bound - 1)) (bounded_exec ex bound)) as Hpre.
    { apply (two_ord_bounds_pre _ _ _ Hval). lia. }
    rewrite (rb_prefix_incl Hpre). kat.
Qed.

Ltac solve_trt_bounds := (simpl_trt; auto; unfold NLE; lia).

Lemma be_union_bound_min_one (ex: Execution) (bound: nat) (x y: Event):
  ((sb (bounded_exec ex bound) ⊔
    rf (bounded_exec ex bound) ⊔
    mo (bounded_exec ex bound) ⊔
    rb (bounded_exec ex bound)) \
   (sb (bounded_exec ex (bound-1)) ⊔
    rf (bounded_exec ex (bound-1)) ⊔
    mo (bounded_exec ex (bound-1)) ⊔
    rb (bounded_exec ex (bound-1)))) x y ->
  (numbering ex x) = bound \/ (numbering ex y) = bound.
Proof.
  intros [H Hnot].
  destruct (Compare_dec.lt_eq_lt_dec (numbering ex x) bound) as [[Hordx|Hordx]|Hordx];
  destruct (Compare_dec.lt_eq_lt_dec (numbering ex y) bound) as [[Hordy|Hordy]|Hordy].
  - exfalso. apply Hnot.
    unfold rb. unfold rb in H. rew bounded. rew bounded in H.
    destruct H as [[[H|H]|H]|H].
    + left; left; left. apply simpl_trt_rel in H. solve_trt_bounds.
    + left; left; right. apply simpl_trt_rel in H. solve_trt_bounds.
    + left; right. apply simpl_trt_rel in H. solve_trt_bounds.
    + right. destruct H as [z Hrf Hmo]. exists z.
      * apply simpl_trt_rel in Hrf. rewrite <- cnv_rev.
        apply rf_num_ord in Hrf as Hordz. solve_trt_bounds.
      * apply simpl_trt_rel in Hmo. apply simpl_trt_rel in Hrf.
        apply rf_num_ord in Hrf as Hordz. solve_trt_bounds.
  - right; auto.
  - exfalso. unfold rb in H. rew bounded in H. destruct H as [[[H|H]|H]|H];
    try (apply simpl_trt_tright in H; unfold NLE in H; lia).
    destruct H as [z _ H]. apply simpl_trt_tright in H. unfold NLE in H. lia.
  - left; auto.
  - left; auto.
  - left; auto.
  - exfalso. unfold rb in H. rew bounded in H. destruct H as [[[H|H]|H]|H];
    try (apply simpl_trt_hyp in H; unfold NLE in H; lia).
    destruct H as [z H _]. apply simpl_trt_hyp in H. unfold NLE in H. lia.
  - right; auto.
  - exfalso. unfold rb in H. rew bounded in H. destruct H as [[[H|H]|H]|H];
    try (apply simpl_trt_hyp in H; unfold NLE in H; lia).
    destruct H as [z H _]. apply simpl_trt_hyp in H. unfold NLE in H. lia.
Qed.

Lemma mcp_write_cycle (ex: Execution) (bound: nat) (k j: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound j k ->
  (numbering ex k) > (numbering ex j) ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  (sb (bounded_exec ex bound) ⊔ rf (bounded_exec ex bound) ⊔ 
   mo (bounded_exec ex bound) ⊔ rb (bounded_exec ex bound))^+ k k.
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hnotsc.
  inversion Hcomp as [Hval _].
  assert (sc_consistent (bounded_exec ex (bound-1))) as Hsc.
  { eapply smaller_than_smallest_sc; eauto.
    inversion Hmcp as [Hscb _].
    erewrite S_min_one. { auto. }
    eapply mcp_bound_gt_zero. eauto. }
  unfold sc_consistent in *.
  apply not_and_or in Hnotsc as [Hnotat | Hcyc].
  { apply (bounded_is_rc11 _ bound Hval) in Hrc11 as [_ [Hat _]].
    intuition auto. }
  apply not_acyclic_is_cyclic in Hcyc.
  destruct Hsc as [_ Hsc].
  rewrite (be_decomposable _ _ Hval (mcp_bound_gt_zero _ _ _ _ Hmcp)) in Hcyc.
  destruct Hcyc as [x Hcyc].
  pose proof (added_cycle_pass_through_addition _ _ _ Hsc Hcyc) as H.
  destruct H as [z1 [z2 Hbegin Hmid] Hend].
  rewrite <- (be_decomposable _ _ Hval (mcp_bound_gt_zero _ _ _ _ Hmcp)) in Hbegin, Hend.
  inversion Hmid as [Hz1z2 _].
  pose proof (be_union_bound_min_one _ _ _ _ Hmid) as [Hz|Hz]; clear Hmid;
  apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp as Hk;
  rewrite (max_rewrite _ _ Hord) in Hk;
  rewrite <-Hk in Hz; rewrite <-numbering_injective_eq in Hz; rewrite <-Hz.
  - rewrite tc_inv_dcmp2. exists z1. { auto. }
    apply rtc_trans. exists x; auto.
  - rewrite tc_inv_dcmp. exists z2; auto.
    apply rtc_trans. exists x; auto.
Qed.

Lemma mcp_write_1 (ex: Execution) (bound: nat) (k j: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound j k ->
  (numbering ex k) > (numbering ex j) ->
  is_write k ->
  (* This condition is here, because this lemma will be applied in a context
  where we assume a program whose SC-executions contain only races relating two
  SC-events. But here, (bounded_exec ex bound) is an execution of the program 
  and it contains a race between events who are not both SC, so it can't be
  an SC-execution *)
  ~(sc_consistent (bounded_exec ex bound)) ->
  exists c, (mo (bounded_exec ex bound)) k c /\ 
            (sb (bounded_exec ex bound) ⊔ rf (bounded_exec ex bound) ⊔ 
             mo (bounded_exec ex bound) ⊔ rb (bounded_exec ex bound))^+ c k.
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hwk Hnotsc.
  inversion Hcomp as [Hval _].
  pose proof (mcp_write_cycle _ _ _ _ Hcomp Hrc11 Hmcp Hord Hnotsc).
  rewrite tc_inv_dcmp3 in H. destruct H as [H|H].
  { pose proof (sbrfmorb_irr _ Hcomp) as Hirr.
    rewrite <-irreflexive_is_irreflexive in Hirr.
    exfalso. apply (Hirr k).
    apply cycle_be_incl_cycle_ex in H. auto. }
  destruct H as [c H1 H2]. exists c; apply conj; auto.
  destruct H1 as [[[Hsb|Hrf]|Hmo]|Hrb].
  - exfalso. eapply (mcp_sb_last ex bound k j); eauto.
    apply mcp_is_sym. auto.
  - exfalso. eapply (mcp_rf_last ex bound k j); eauto.
    apply mcp_is_sym. auto.
  - auto.
  - destruct Hrb as [z Hrf _].
    rewrite <-cnv_rev in Hrf.
    eapply rf_dest_read in Hrf.
    + exfalso. destruct k; auto.
    + apply bounded_is_valid. auto.
Qed.

Lemma sbrfmorb_to_write (ex: Execution) (x y: Event):
  valid_exec ex ->
  is_write y ->
  (sb ex ⊔ rf ex ⊔ mo ex ⊔ rb ex) x y ->
  (sb ex ⊔ mo ex ⊔ rb ex) x y.
Proof.
  intros Hval Hw Hr.
  rewrite 2(union_comm_assoc _ (rf ex) _) in Hr.
  destruct Hr as [Hr|Hr]; auto.
  apply (rf_dest_read _ Hval) in Hr.
  destruct y; simpl in *; intuition auto.
Qed.

Lemma sbrfmorb_bound_right (ex: Execution) (bound: nat) (x y: Event):
  (sb (bounded_exec ex bound) ⊔
   rf (bounded_exec ex bound) ⊔
   mo (bounded_exec ex bound) ⊔
   rb (bounded_exec ex bound)) x y ->
  (numbering ex y) <= bound.
Proof.
  intros Hr. byabsurd.
  unfold rb in Hr. destruct Hr as [[[Hr|Hr]|Hr]|Hr];
  rew bounded in Hr.
  - apply simpl_trt_tright in Hr. unfold NLE in Hr. lia.
  - apply simpl_trt_tright in Hr. unfold NLE in Hr. lia.
  - apply simpl_trt_tright in Hr. unfold NLE in Hr. lia.
  - destruct Hr as [z _ Hr]. 
    apply simpl_trt_tright in Hr. unfold NLE in Hr. lia.
Qed.

Lemma mcp_write_2 (ex: Execution) (bound: nat) (k j c: Event):
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound j k ->
  (numbering ex k) > (numbering ex j) ->
  is_write k ->
  (numbering ex c) < bound ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  (sb (bounded_exec ex bound) ⊔
   rf (bounded_exec ex bound) ⊔
   mo (bounded_exec ex bound) ⊔ 
   rb (bounded_exec ex bound))^+ c k ->
  exists d, (sb (bounded_exec ex (bound-1)) ⊔
             rf (bounded_exec ex (bound-1)) ⊔
             mo (bounded_exec ex (bound-1)) ⊔
             rb (bounded_exec ex (bound-1)))^* c d /\
            (sb (bounded_exec ex bound) ⊔ 
             mo (bounded_exec ex bound) ⊔ 
             rb (bounded_exec ex bound)) d k.
Proof.
  intros Hval Hrc11 Hmcp Hord Hw Hc Hnotsc (*Hkc*) Hck.
  rewrite (be_decomposable _ _ Hval (mcp_bound_gt_zero _ _ _ _ Hmcp)) in Hck.
  rewrite tc_union_dcmp in Hck.
  destruct Hck as [Hck|Hck].
  { rewrite tc_inv_dcmp in Hck. destruct Hck as [z _ Hck].
    apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp.
    rewrite (max_rewrite _ _ Hord) in Hmcp.
    apply sbrfmorb_bound_right in Hck. lia.
  }
  destruct Hck as [w1 [w2 H1 H2] _].
  exists w2. split. auto.
  rewrite rtc_inv_dcmp6 in H1.
  destruct H1 as [H1|H1].
  - simpl in H1. rewrite <-H1 in H2.
    apply be_union_bound_min_one in H2 as Hcw1.
    destruct Hcw1. 
    + lia.
    + apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp.
      rewrite (max_rewrite _ _ Hord) in Hmcp.
      rewrite <-H in Hmcp. apply numbering_injective_eq in Hmcp.
      rewrite Hmcp. rewrite <-H1. destruct H2 as [H2 _].
      rewrite Hmcp in Hw. eapply sbrfmorb_to_write; auto.
      apply bounded_is_valid. auto.
  - apply be_union_bound_min_one in H2 as Hw1w2.
    destruct Hw1w2 as [Hw2|Hw1].
    + rewrite tc_inv_dcmp in H1. destruct H1 as [w3 _ H1].
      apply sbrfmorb_bound_right in H1. lia.
    + apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp.
      rewrite (max_rewrite _ _ Hord) in Hmcp.
      rewrite <-Hw1 in Hmcp. apply numbering_injective_eq in Hmcp.
      rewrite <- Hmcp in H2. apply minus_incl in H2.
      apply sbrfmorb_to_write  in H2; auto.
      apply bounded_is_valid. auto.
Qed.

Lemma mcp_write_not_at (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex y) > (numbering ex x) ->
  is_write y ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  ~(In _ (At (bounded_exec ex bound)) y).
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hxw Hnotsc Hnot.
  inversion Hcomp as [Hval _].
  assert (valid_exec (bounded_exec ex bound)) as Hvalb.
  { apply bounded_is_valid. auto. }
  assert (complete_exec (bounded_exec ex bound)) as Hcompb.
  { apply bounded_is_complete. auto. }
  destruct Hnot as [y [b Hrmw] | y [b Hrmw]].
  - apply (rmw_orig_read _ Hvalb) in Hrmw.
    destruct y; intuition auto.
  - destruct (mcp_write_1 _ _ _ _ Hcomp Hrc11 Hmcp Hord Hxw Hnotsc) as [c [Hyc Hcy]].
    pose proof (mcp_num_snd_evt _ _ _ _ Hval Hmcp) as Hybound.
    rewrite (max_rewrite _ _ Hord) in Hybound.

    assert (numbering ex c < bound) as Hordc.
    { destruct (Compare_dec.lt_eq_lt_dec bound (numbering ex c)) as [[H'|H']|H'].
      - apply simpl_trt_tright in Hyc. unfold NLE in Hyc. lia.
      - rewrite <-Hybound in H'. apply numbering_injective_eq in H'.
        rewrite <-H' in Hyc. exfalso. eapply (mo_irr (bounded_exec ex bound)).
        + apply bounded_is_complete. auto.
        + split. eauto. split.
      - lia.
    }

    eapply (mcp_write_2 _ _ _ _ _ Hval Hrc11 Hmcp Hord Hxw Hordc Hnotsc) 
    in Hcy as [d [Hcd Hdy]].

    inversion Hmcp as [Hscb _].

    assert (numbering ex b < bound) as Hordb.
    { apply rmw_incl_sb in Hrmw.
      - apply sb_num_ord in Hrmw.
        rewrite 2(numbering_pre_stable _ _ (bounded_exec_is_prefix _ bound Hval)) in Hrmw.
        lia.
      - apply bounded_is_valid. auto.
    }

    unshelve (epose proof (smaller_than_smallest_sc _ _ Hcomp Hrc11 Hscb (bound-1) _) as Hsc).
    { apply mcp_bound_gt_zero in Hmcp. lia. }

    assert (numbering ex d < bound) as Hordd.
    { destruct (Compare_dec.lt_eq_lt_dec bound (numbering ex d)) as [[H'|H']|H'].
      - destruct Hdy as [[Hdy|Hdy]|Hdy].
        + apply simpl_trt_hyp in Hdy as [Hdy _]. unfold NLE in *. lia.
        + apply simpl_trt_hyp in Hdy as [Hdy _]. unfold NLE in *. lia.
        + unfold rb in Hdy. destruct Hdy as [z Hdy _]. rewrite <-cnv_rev in Hdy.
          apply simpl_trt_tright in Hdy. unfold NLE in *. lia.
      - rewrite H' in Hybound. rewrite <-numbering_injective_eq in Hybound.
        rewrite Hybound in Hdy. destruct Hdy as [[Hdy|Hdy]|Hdy]; exfalso.
        + eapply ((proj2 (irreflexive_is_irreflexive _)) (sb_irr _ Hcompb)). eauto.
        + eapply ((proj2 (irreflexive_is_irreflexive _)) (mo_irr _ Hcompb)). eauto.
        + eapply ((proj2 (irreflexive_is_irreflexive _)) (rb_irr _ Hcompb)). eauto.
      - lia.
    }
    rewrite <-union_assoc in Hdy. destruct Hdy as [Hdy|Hdy].

    + apply (rmw_incl_imm_sb _ Hvalb) in Hrmw as Himm.
      destruct Himm as [Hr Himm].
      destruct (Himm d Hdy) as [Hdb _].
      assert ((rb (bounded_exec ex (bound-1))) b c) as Hbc.
      { eapply rc11_rmw_incl_rb in Hrmw.
        - destruct Hrmw as [z Hrfinv Hmo].
          assert (numbering ex z < bound).
          { apply simpl_trt_rel, rf_num_ord in Hrfinv. lia. }
          exists z.
          + rew bounded. rew bounded in Hrfinv.
            rewrite <-cnv_rev. rewrite <- cnv_rev in Hrfinv.
            apply simpl_trt_rel in Hrfinv. solve_trt_bounds.
          + rew bounded. rew bounded in Hyc.
            apply simpl_trt_rel in Hyc.
            apply simpl_trt_rel in Hmo. 
            exists c. exists z.
            * split. auto. unfold NLE. lia.
            * auto. apply mo_trans with y; auto.
            * split. auto. unfold NLE. lia.
        - apply bounded_is_complete. auto.
        - apply bounded_is_rc11; auto.
      }
      assert ((sb (bounded_exec ex (bound-1)) ?) d b) as Hdbminone.
      { destruct Hdb as [Hdb|Hdb].
        - apply simpl_trt_rel in Hdb. left. rew bounded. solve_trt_bounds.
        - right. auto.
      }
      destruct Hsc as [_ Hac].
      apply (Hac d).
      rewrite rtc_inv_dcmp6 in Hcd.
      destruct Hdbminone as [Hdbminone|Hdbminone];
      destruct Hcd as [Hcd|Hcd].
      { simpl in Hcd. rewrite Hcd in Hbc.
        apply tc_trans with b.
        - incl_rel_kat Hdbminone.
        - incl_rel_kat Hbc.
      }
      { apply tc_trans with c. apply tc_trans with b.
        - incl_rel_kat Hdbminone.
        - incl_rel_kat Hbc.
        - auto.
      }
      { simpl in Hdbminone, Hcd.
        rewrite <-Hdbminone in Hbc. rewrite Hcd in Hbc.
        exfalso. eapply rb_irr.
        - eapply (bounded_is_complete _ (bound-1)). eapply Hcomp.
        - split. eauto. simpl. auto.
      }
      { simpl in Hdbminone. rewrite <-Hdbminone in Hbc.
        apply tc_trans with c.
        - incl_rel_kat Hbc.
        - incl_rel_kat Hcd.
      }
    + assert ((mo (bounded_exec ex (bound-1)) ⊔ rb (bounded_exec ex (bound-1))) d c) as Hdc.
      { destruct Hdy as [Hdy|Hdy].
        - left. rew bounded. simpl_trt; try (unfold NLE; lia).
          apply simpl_trt_rel in Hdy. apply simpl_trt_rel in Hyc.
          apply (mo_trans _ Hval) with y; auto.
        - destruct Hdy as [z Hrfinv Hmo]. rewrite <-cnv_rev in Hrfinv.
          assert (numbering ex z < bound).
          { apply rf_num_ord in Hrfinv.
            rewrite 2(numbering_pre_stable _ _ (bounded_exec_is_prefix _ bound Hval)) in Hrfinv.
            lia.
          }
          right. exists z.
          + rewrite <-cnv_rev. apply simpl_trt_rel in Hrfinv.
            rew bounded. solve_trt_bounds.
          + rew bounded. simpl_trt; try (unfold NLE; lia).
            apply simpl_trt_rel in Hyc. apply simpl_trt_rel in Hmo.
            apply (mo_trans _ Hval) with y; auto.
      }
      rewrite rtc_inv_dcmp6 in Hcd.
      destruct Hsc as [_ Hac].
      destruct (Hac d).
      destruct Hcd as [Hcd|Hcd].
      * simpl in Hcd. rewrite Hcd in Hdc.
        incl_rel_kat Hdc.
      * apply tc_trans with c.
        -- incl_rel_kat Hdc.
        -- incl_rel_kat Hcd.
Qed.


(** This transformation is meaningful only when [y] is a write event whose
numbering is equal to [bound], and if [bound] is the smallest conflicting
bounding of the execution.

The result of the transformation is an execution where the events, the
sequenced-before, read-modify-write and read-from relation don't change, but
where the write event is after all the other write events in the modification
order. This means that the write is visible to all the threads of the execution
after all the other writes events *)

Definition prefix_change_mo (ex: Execution) (bound: nat) (y: Event) :=
  mkex (evts (bounded_exec ex bound))
       (sb   (bounded_exec ex bound))
       (rmw  (bounded_exec ex (bound-1)))
       (rf   (bounded_exec ex (bound-1)))
       (mo   (bounded_exec ex (bound-1)) ⊔ (fun a b => (b = y) /\
                   (In _ (evts (bounded_exec ex (bound-1))) a) /\
                   (is_write a) /\
                   (get_loc a) = (get_loc y))).

Lemma simpl_evts_change_mo (ex: Execution) (bound: nat) (y: Event):
  evts (prefix_change_mo ex bound y) = evts (bounded_exec ex bound).
Proof. compute; auto. Qed.

Lemma simpl_sb_change_mo (ex: Execution) (bound: nat) (y: Event):
  sb (prefix_change_mo ex bound y) = sb (bounded_exec ex bound).
Proof. compute; auto. Qed.

Lemma simpl_rmw_change_mo (ex: Execution) (bound: nat) (y: Event):
  rmw (prefix_change_mo ex bound y) = rmw (bounded_exec ex (bound-1)).
Proof. compute; auto. Qed.

Lemma simpl_rf_change_mo (ex: Execution) (bound: nat) (y: Event):
  rf (prefix_change_mo ex bound y) = rf (bounded_exec ex (bound-1)).
Proof. compute; auto. Qed.

Lemma simpl_mo_change_mo (ex: Execution) (bound: nat) (y: Event):
  mo (prefix_change_mo ex bound y) =
    mo (bounded_exec ex (bound-1)) ⊔ (fun a b => (b = y) /\
                   (In _ (evts (bounded_exec ex (bound-1))) a) /\
                   (is_write a) /\
                   (get_loc a) = (get_loc y)).
Proof. compute; auto. Qed.

Create HintDb change_mo_db.

Hint Rewrite simpl_evts_change_mo simpl_sb_change_mo simpl_rmw_change_mo
             simpl_rf_change_mo simpl_mo_change_mo : change_mo_db.

Tactic Notation "rew" "change_mo" := autorewrite with change_mo_db.
Tactic Notation "rew" "change_mo" "in" hyp(H) := autorewrite with change_mo_db in H.


Lemma evt_diff_bound (ex: Execution) (bound: nat) (x y w: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  numbering ex y > numbering ex x ->
  In _ (evts (bounded_exec ex bound)) w ->
  w <> y ->
  In _ (evts (bounded_exec ex (bound-1))) w.
Proof.
  intros Hco Hrc11 Hmcp Hord Hin Hdiff.
  inversion Hco as [Hval _].
  rewrite simpl_evts_be in *.
  apply in_intersection in Hin as [Hevts Hnumw].
  split; auto.
  unfold In in *.
  destruct (Compare_dec.lt_eq_lt_dec bound (numbering ex w)) as [[Hord1|Hord1]|Hord1].
  - lia.
  - pose proof (mcp_num_snd_evt _ _ _ _ Hval Hmcp) as Hnumy.
    rewrite (max_rewrite _ _ Hord) in Hnumy.
    rewrite Hord1 in Hnumy. apply numbering_injective_eq in Hnumy.
    congruence.
  - lia.
Qed.

Lemma mo_change_complete (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex y) > (numbering ex x) ->
  is_write y ->
  complete_exec (prefix_change_mo ex bound y).
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hw.
  inversion Hcomp as [Hval _]; inverse_val_exec Hval.
  split;[split;[|split;[|split;[|split]]]|]; rew change_mo.
  - eapply prefix_evts_valid. eauto. apply bounded_exec_is_prefix. auto.
  - eapply prefix_sb_valid. eauto. apply bounded_exec_is_prefix. auto.
  - eapply prefix_rmw_valid_diff_evts.
    + eauto.
    + apply two_ord_bounds_pre. auto. apply mcp_bound_gt_zero in Hmcp. lia.
    + apply bounded_exec_is_prefix. auto.
  - eapply prefix_rf_valid_diff_evts.
    + eauto.
    + apply two_ord_bounds_pre. auto. apply mcp_bound_gt_zero in Hmcp. lia.
    + apply bounded_exec_is_prefix. auto.
  - assert (valid_exec (bounded_exec ex (bound-1))) as Hvalbmin1.
    { eapply bounded_is_valid. auto. }
    assert (valid_exec (bounded_exec ex bound)) as Hvalbmin2.
    { eapply bounded_is_valid. auto. }
    assert (prefix (bounded_exec ex (bound-1)) (bounded_exec ex bound)) as Hpre.
    { eapply two_ord_bounds_pre. auto. apply mcp_bound_gt_zero in Hmcp. lia. }
    repeat (apply conj).
    + apply ext_rel, antisym; intros w z H.
      auto using (simpl_trt_rel _ _ _ _ _ H).
      simpl_trt; auto.
      * destruct H as [H|H];[|intuition auto].
        destruct Hvalbmin1 as [_ [_ [_ [_ [Hmo_v1 _]]]]].
        rewrite <-Hmo_v1 in H. destruct H as [? [? [_ H]]]. auto.
      * destruct H as [H|H];[|destruct H as [Hzy _]; rewrite Hzy; auto].
        destruct Hvalbmin1 as [_ [_ [_ [_ [Hmo_v1 _]]]]].
        rewrite <-Hmo_v1 in H. destruct H as [? _ [Heq Hwz]].
        rewrite <-Heq. auto.
    + intros w z [Hmo|Hext].
      * destruct Hvalbmin1 as [_ [_ [_ [_ [_ [Hmo_v1 _]]]]]].
        apply Hmo_v1. auto.
      * destruct Hext as [Heq [_ [_ Hloc]]].
        rewrite Heq. auto.
    + apply ext_rel, antisym; intros w z H; 
      [|auto using (simpl_trt_rel _ _ _ _ _ H)].
      simpl_trt; auto.
      * destruct H as [H|H];
        [inversion Hvalbmin1 as [_ [_ [_ [_ Hmo_v1]]]];
         apply (mo_orig_evts _ Hvalbmin1) in H | destruct H as [_ [H _]]];
        eapply prefix_incl_evts; eauto.
      * destruct H as [H|H].
        -- inversion Hvalbmin1 as [_ [_ [_ [_ Hmo_v1]]]].
           eapply (mo_dest_evts _ Hvalbmin2).
           eapply mo_prefix_incl. eauto. eauto.
        -- destruct H as [H _]. rewrite H.
           eapply mcp_in_evts_right. eauto.
    + intros w1 w2 [z [H1|H1] [H2|H2]].
      * left. eapply mo_trans with z; eauto.
      * right. destruct H2 as [Heqw2 [Hinz [Hwz Heqloc]]].
        repeat (apply conj).
        -- auto.
        -- eapply mo_orig_evts; eauto.
        -- eapply mo_orig_write. eapply Hvalbmin1. eauto.
        -- rewrite <-Heqloc. eapply mo_same_loc. eapply Hvalbmin1. eauto.
      * destruct H1 as [H1 _].
        rewrite H1 in H2. rew bounded in H2.
        apply simpl_trt_hyp in H2 as [H2 _].
        apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp.
        rewrite (max_rewrite _ _ Hord) in Hmcp.
        unfold NLE in H2. rewrite Hmcp in H2. lia.
      * right. intuition auto.
    + intros w1 [Hnot|Hnot].
      * destruct Hvalbmin1 as [_ [_ [_ [_ Hmo_v1]]]].
        destruct Hmo_v1 as [_ [_ [[_ [_ Hmo_v1]] _]]].
        apply (Hmo_v1 w1). auto.
      * destruct Hnot as [Heq [Hin _]].
        rewrite Heq in Hin.
        apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp.
        rewrite (max_rewrite _ _ Hord) in Hmcp.
        rewrite simpl_evts_be in Hin. apply in_intersection in Hin as [_ Hin].
        unfold In in Hin. rewrite Hmcp in Hin. lia.
    + intros l. intros w1 w2 Hdiff Hin1 Hin2.
      destruct (classic (w1 = y)) as [Hw1|Hw1];
      destruct (classic (w2 = y)) as [Hw2|Hw2].
      * rewrite Hw1, Hw2 in Hdiff. intuition auto.
      * right. split.
        -- right. repeat (apply conj).
          ++ auto.
          ++ apply writes_loc_evts in Hin2.
             apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hmcp Hord Hin2 Hw2).
          ++ apply (writes_loc_is_write _ _ _ Hin2).
          ++ apply writes_loc_loc in Hin1.
             apply writes_loc_loc in Hin2.
             rewrite <-Hw1, Hin1. auto.
        -- split; eapply writes_loc_loc; eauto.
      * left. split.
        -- right. repeat (apply conj).
           ++ auto.
           ++ apply writes_loc_evts in Hin1.
              apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hmcp Hord Hin1 Hw1).
           ++ apply (writes_loc_is_write _ _ _ Hin1).
           ++ apply writes_loc_loc in Hin1.
              apply writes_loc_loc in Hin2.
              rewrite <-Hw2, Hin2. auto.
        -- split; eapply writes_loc_loc; eauto.
      * apply writes_loc_evts in Hin1 as Hw1evts.
        apply writes_loc_evts in Hin2 as Hw2evts.
        destruct_mo_v Hmo_v.
        edestruct Hmotot as [Hmow1w2|Hmow2w1].
        -- eapply Hdiff.
        -- destruct Hin1 as [Hin1 [Hw1w Hloc1]].
           rewrite simpl_evts_be in Hin1.
           apply in_intersection in Hin1 as [Hin1 _].
           repeat (apply conj); eauto.
        -- destruct Hin2 as [Hin2 [Hw2w Hloc2]].
           rewrite simpl_evts_be in Hin2.
           apply in_intersection in Hin2 as [Hin2 _].
           repeat (apply conj); eauto.
        -- left. repeat (apply conj).
           ++ left. rew bounded. simpl_trt.
             ** apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hmcp Hord Hw1evts) in Hw1.
                unfold In in Hw1. rewrite simpl_evts_be in Hw1.
                apply in_intersection in Hw1 as [_ Hw1].
                unfold In in Hw1. unfold NLE. lia.
             ** destruct Hmow1w2. auto.
             ** apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hmcp Hord Hw2evts) in Hw2.
                unfold In in Hw2. rewrite simpl_evts_be in Hw2.
                apply in_intersection in Hw2 as [_ Hw2].
                unfold In in Hw2. unfold NLE. lia.
           ++ apply writes_loc_loc in Hin1. auto.
           ++ apply writes_loc_loc in Hin2. auto.
        -- right. repeat (apply conj).
           ++ left. rew bounded. simpl_trt.
             ** apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hmcp Hord Hw2evts) in Hw2.
                unfold In in Hw2. rewrite simpl_evts_be in Hw2.
                apply in_intersection in Hw2 as [_ Hw2].
                unfold In in Hw2. unfold NLE. lia.
             ** destruct Hmow2w1. auto.
             ** apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hmcp Hord Hw1evts) in Hw1.
                unfold In in Hw1. rewrite simpl_evts_be in Hw1.
                apply in_intersection in Hw1 as [_ Hw1].
                unfold In in Hw1. unfold NLE. lia.
           ++ apply writes_loc_loc in Hin2. auto.
           ++ apply writes_loc_loc in Hin1. auto.
  - intros z [Hzevts Hzread].
    assert (z <> y) as Hdiff.
    { destruct (classic (y = z)); auto.
      rewrite H in Hw. destruct z; auto. }
    pose proof (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hmcp Hord Hzevts Hdiff) as Hzb1.
    destruct Hcomp as [_ Hcomp].
    rewrite simpl_evts_be in Hzevts.
    apply in_intersection in Hzevts as [Hzevts _].
    edestruct Hcomp as [w H].
    + split; eauto.
    + exists w. rew bounded.
      rewrite simpl_evts_be in Hzb1.
      apply in_intersection in Hzb1 as [_ Hordz].
      simpl_trt; unfold NLE; unfold In in *.
      * apply rf_num_ord in H. lia.
      * auto.
Qed.

(*
Lemma sc_racy_exec (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex y) > (numbering ex x) ->
  is_write y ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  sc_consistent (prefix_change_mo ex bound y).
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hw Hnotsc.
  unfold.
*)

End DRF.













