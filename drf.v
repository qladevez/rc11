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
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex y) > (numbering ex x) ->
  (sb ex) b y ->
  ~((sb ex ⊔ rf ex)^+ x b).
Proof.
  intros Hval Hrc11 Hmcp Hord Hsb.
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
    + eapply prefix_valid; eauto.
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
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) > (numbering ex y) ->
  is_write x ->
  race (bounded_exec ex bound) x y.
Proof.
  intros Hval Hrc11 Hmcp Hord Hw.
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
      * apply bounded_is_valid; auto.
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
    + apply bounded_is_valid. auto.
Qed.

(** Under the hypothesis that every race in every SC-consistent execution of a 
program is between two SC events, then the minimal conflicting execution where
the conflicting event with the highest numbering is a write event is not
SC-consistent *)

Lemma mcp_write_not_sc (ex: Execution) (bound: nat) (x y: Event):
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) > (numbering ex y) ->
  is_write x ->
  (forall pre, prefix pre ex ->
               forall j k, race pre j k ->
                           ((get_mode j) = Sc /\ (get_mode k) = Sc)) ->
  ~(sc_consistent (bounded_exec ex bound)).
Proof.
  intros Hval Hrc11 Hmcp Hord Hwx Hrace_not_sc Hnot.
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
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound j k ->
  (numbering ex k) > (numbering ex j) ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  (sb (bounded_exec ex bound) ⊔ rf (bounded_exec ex bound) ⊔ 
   mo (bounded_exec ex bound) ⊔ rb (bounded_exec ex bound))^+ k k.
Proof.
  intros Hval Hrc11 Hmcp Hord Hnotsc.
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

Lemma mcp_write_1 (ex: Execution) (bound: nat) (k j b: Event):
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound j k ->
  (numbering ex k) > (numbering ex j) ->
  is_write k ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  (rmw ex) b k ->
  exists c, (mo ex) k c /\ (sb ex ⊔ rf ex ⊔ mo ex ⊔ rb ex)^+ c k.
Proof.
  intros Hval Hrc11 Hmcp Hord Hwk Hnotsc Hrmw.
  pose proof (mcp_write_cycle _ _ _ _ Hval Hrc11 Hmcp Hord Hnotsc).
  rewrite tc_inv_dcmp3 in H. destruct H as [H|H].
  { pose proof (sbrfmorb_irr _ Hval) as Hirr.
    rewrite <-irreflexive_is_irreflexive in Hirr.
    exfalso. apply (Hirr k).
    apply cycle_be_incl_cycle_ex in H. auto. }
  destruct H as [c H1 H2]. exists c; apply conj; auto.
  destruct H1 as [[[Hsb|Hrf]|Hmo]|Hrb].
  - exfalso. eapply (mcp_sb_last ex bound k j); eauto.
    apply mcp_is_sym. auto.
  - exfalso. eapply (mcp_rf_last ex bound k j); eauto.
    apply mcp_is_sym. auto.
  - eapply mo_prefix_incl.
    + eapply bounded_exec_is_prefix. auto.
    + eauto.
  - destruct Hrb as [z Hrf _].
    rewrite <-cnv_rev in Hrf.
    eapply rf_dest_read in Hrf.
    + exfalso. destruct k; auto.
    + apply bounded_is_valid. auto.
  - apply (tc_incl _ _ (cycle_be_incl_cycle_ex _ _))in H2. auto.
Qed.

Lemma mcp_write_not_at (ex: Execution) (bound: nat) (x y: Event):
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) > (numbering ex y) ->
  is_write x ->
  ~(In _ (At ex) x).
Proof.
  intros Hval Hrc11 Hmcp Hord Hxw Hnot.
  destruct Hnot as [x [z Hrmw] | x [z Hrmw]].
  - eapply (rmw_orig_read _ Hval) in Hrmw.
    destruct x; intuition auto.
  - admit.
Admitted.

End DRF.













