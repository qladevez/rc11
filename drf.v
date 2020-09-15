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

(** For any execution, race is a symmetric relation *)

Lemma race_sym (ex: Execution) (x y: Event):
  race ex x y <-> race ex y x.
Proof. compute; intuition. Qed.

Module DRF.

(** If a bound gives the minimal conflicting pair of an execution, it is greater
than 0 *)

Lemma mcp_bound_gt_zero (ex: Execution) (bound: nat) (k j: Event):
  numbering_injective ex ->
  minimal_conflicting_pair ex bound k j ->
  bound > 0.
Proof.
  intros Hnuminj Hmcp.
  apply mcp_in_evts_left in Hmcp as Hinl.
  apply mcp_in_evts_right in Hmcp as Hinr.
  destruct Hinl as [z Hevts Hord].
  destruct Hinr as [z' Hevts' Hord'].
  unfold In in Hord, Hord'.
  apply mcp_diff in Hmcp.
  apply (Hnuminj _ _ ) in Hmcp.
  lia.
Qed.

(** If a bound gives the minimal conflicting pair of an execution, we can
substract one to the bound and obtain a smaller bound *)

Lemma mcp_bound_min_one_lt_bound (ex: Execution) (bound: nat) (k j: Event):
  numbering_injective ex ->
  minimal_conflicting_pair ex bound k j ->
  bound - 1 < bound.
Proof.
  intros Hnuminj Hmcp.
  assert (bound > 0). eauto using mcp_bound_gt_zero.
  lia.
Qed.

(** If two events are sequenced in an execution, and if the latest event's
numbering is smaller than a bound, they are still sequenced in the bounding
of the execution by the bound *)

Lemma sb_bounded (ex: Execution) (b: nat) (x y: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  (sb ex) x y ->
  (numbering y) <= b ->
  (sb (bounded_exec ex b)) x y.
Proof.
  intros Hval Hnumco Hsb Hord. rew bounded.
  exists y. exists x; auto.
  - split; auto.
    apply (sb_num_ord _ _ _ Hnumco) in Hsb.
    unfold NLE. lia.
  - split; auto.
Qed.

(** If a read reads it value from a write, and if the write's
numbering is smaller than a bound, the read still reads its value from its
write in the bounding of the execution by the bound *)

Lemma rf_bounded (ex: Execution) (b: nat) (x y: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  (rf ex) x y ->
  (numbering y) <= b ->
  (rf (bounded_exec ex b)) x y.
Proof.
  intros Hval Hnumco Hrf Hord. rew bounded.
  exists y. exists x; auto.
  - split; auto.
    apply (rf_num_ord _ _ _ Hnumco) in Hrf.
    unfold NLE. lia.
  - split; auto.
Qed.

(** If two events [x] and [y] are related by the transitive closure of the union of 
sequenced-before and read-from, and if the numbering of [y] is inferior to a
a bound, then the two events are still related by the same relation in the
bounding of the execution by the bound *)

Lemma sbrf_boundable' (ex: Execution) (b: nat):
  valid_exec ex ->
  numbering_coherent ex ->
  forall (x y: Event),
  (sb ex ⊔ rf ex)^+ x y ->
  (fun j k => b >= (numbering y) ->
              (sb (bounded_exec ex b) ⊔ rf (bounded_exec ex b))^+ x y) x y.
Proof.
  intros Hval Hnumco.
  apply tc_ind.
  - intros x y Hsbrf Hord. apply tc_incl_itself.
    destruct Hsbrf as [Hsb|Hrf].
    + left. eauto using sb_bounded.
    + right. eauto using rf_bounded.
  - intros x y z Hrxy IHrxy Hryz IHryz Hord.
    apply tc_trans with y.
    + apply IHrxy.
      apply (numbering_coherent_tc _ _ _ Hnumco) in Hryz. lia.
    + apply IHryz. auto.
Qed.

Lemma sbrf_boundable (ex: Execution) (b: nat):
  valid_exec ex ->
  numbering_coherent ex ->
  forall (x y: Event),
  (sb ex ⊔ rf ex)^+ x y ->
  b >= (numbering y) ->
  (sb (bounded_exec ex b) ⊔ rf (bounded_exec ex b))^+ x y.
Proof. apply sbrf_boundable'. Qed.

(** In a valid and rc11-consistent execution with a miniaml conflicting pair, 
any event sequenced before the biggest event of the conflicting pair, is not
related to the smallest event of the conflicting pair by the transitive closure
of the union of sequence-before and reads-from *)

Lemma sbbefore_lemma (ex: Execution) (bound: nat) (x y b: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering y) > (numbering x) ->
  (sb ex) b y ->
  ~((sb ex ⊔ rf ex)^+ x b).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hsb.
  inversion Hcomp as [Hval _].
  eapply mcp_not_sbrfsc in Hmcp as Hnotsbrfsc.
  intros Hnot; apply Hnotsbrfsc.
  apply tc_trans with b.
  - assert (bound >= numbering b) as Hordbndb.
    { transitivity (numbering y).
      - eauto using mcp_right_le_bound.
      - enough (numbering y > numbering b). lia. eauto using sb_num_ord. }
    eapply sbrfsc_pre_inc.
    { apply two_ord_bounds_pre; eauto.
      eapply mcp_bound_min_one_lt_bound; eauto. }
    apply sbrf_incl_sbrfsc.
    + eapply prefix_complete; eauto.
      eapply bounded_exec_is_prefix; eauto.
    + eapply prefix_rc11_consistent; eauto.
      eapply bounded_exec_is_prefix; eauto.
    + eapply smaller_than_smallest_not_conflicting.
      * destruct Hmcp as [? _]. eauto.
      * eapply mcp_bound_min_one_lt_bound; eauto.
    + eapply sbrf_boundable; eauto.
      eapply (mcp_num_snd_evt _ _ _ _ Hval Hnumco) in Hmcp.
      rewrite (max_rewrite _ _ Hord) in Hmcp.
      rewrite Hmcp in Hord. apply (sb_num_ord _ _ _ Hnumco) in Hsb. lia.
  - apply tc_incl_itself. left. rew bounded.
    exists y. exists b.
    + split; auto. apply (sb_num_ord _ _ _ Hnumco) in Hsb. unfold NLE.
      apply mcp_right_le_bound in Hmcp. lia.
    + auto.
    + split; auto. apply mcp_right_le_bound in Hmcp. unfold NLE. lia.
Qed.

(** In an execution with a minimal conflicting pair, no event can be sequenced
after the event of the conflicting pair with the biggest numbering *)

Lemma mcp_sb_last (ex: Execution) (bound:nat) (x y: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound x y ->
  numbering x > numbering y ->
  (forall z, ~(sb (bounded_exec ex bound) x z)).
Proof.
  intros Hval Hnumco Hmcp Hord z Hsb.
  rew bounded in Hsb.
  apply simpl_trt_hyp in Hsb as [_ [Hsb Htz]].
  apply (mcp_num_snd_evt _ _ _ _ Hval Hnumco) in Hmcp.
  rewrite (max_rewrite' _ _ Hord) in Hmcp.
  apply (sb_num_ord _ _ _ Hnumco) in Hsb. rewrite Hmcp in Hsb.
  unfold NLE in Htz. lia.
Qed.

(** In an execution with a minimal conflicting pair, the event of the 
conflicting pair with the biggest numbering cannot reads its value from 
another event *)

Lemma mcp_rf_last (ex: Execution) (bound:nat) (x y: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound x y ->
  numbering x > numbering y ->
  (forall z, ~(rf (bounded_exec ex bound) x z)).
Proof.
  intros Hval Hnumco Hmcp Hord z Hsb.
  rew bounded in Hsb.
  apply simpl_trt_hyp in Hsb as [_ [Hsb Htz]].
  apply (mcp_num_snd_evt _ _ _ _ Hval Hnumco) in Hmcp.
  rewrite (max_rewrite' _ _ Hord) in Hmcp.
  apply (rf_num_ord _ _ _ Hnumco) in Hsb. rewrite Hmcp in Hsb.
  unfold NLE in Htz. lia.
Qed.

(** ** The first conflicting event is a write event *)

(** If the event of a minimal conflicting pair with the biggest numbering is a
write, the conflicting pair cannot be related by the union of sequenced-before
and reads-from *)

Lemma mcp_write_not_sbrf (ex: Execution) (bound: nat) (x y: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering x) > (numbering y) ->
  is_write x ->
  ~((sb (bounded_exec ex bound) ⊔ rf (bounded_exec ex bound)) y x).
Proof.
  intros Hval Hnumco Hrc11 Hmcp Hord Hw [Hsb|Hsw].
  - eapply mcp_not_cnv_sbrfsc. eauto. eapply tc_incl_itself. left. eauto.
  - apply rf_dest_read in Hsw.
    + destruct x; auto.
    + eapply bounded_is_valid; eauto.
Qed.

(** In a valid, rc11-consistent execution with a minimal conflicting pair, if
the event of the conflicting pair with the biggest numbering is a write event,
the two events form a race in the execution (bounded with the bound of the
minimal conflicting pair *)

Lemma mcp_write_race (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering x) > (numbering y) ->
  is_write x ->
  race (bounded_exec ex bound) x y.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw.
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
      * eapply numbering_coherent_pre. eauto.
        apply bounded_exec_is_prefix; auto.
      * eapply numbering_injective_pre. eauto.
        apply bounded_exec_is_prefix; auto.
      * apply mcp_bounded; auto.
        apply mcp_is_sym. auto.
      * auto.
      * auto.
      * auto.
    + apply rf_dest_read in Hsw. destruct x; auto.
      apply bounded_is_valid; auto.
    + apply bounded_is_complete; auto.
Qed.

(** Under the hypothesis that every race in every SC-consistent execution of a 
program is between two SC events, then the minimal conflicting execution where
the conflicting event with the highest numbering is a write event is not
SC-consistent *)

Lemma mcp_write_not_sc (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering x) > (numbering y) ->
  is_write x ->
  (forall pre, prefix pre ex ->
               sc_consistent pre ->
               forall j k, race pre j k ->
                           ((get_mode j) = Sc /\ (get_mode k) = Sc)) ->
  ~(sc_consistent (bounded_exec ex bound)).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hwx Hrace_not_sc Hnot.
  inversion Hcomp as [Hval _].
  apply (mcp_at_least_one_not_sc ex x y bound Hmcp).
  apply (Hrace_not_sc (bounded_exec ex bound)).
  - eapply bounded_exec_is_prefix; eauto.
  - auto.
  - apply mcp_write_race; auto.
Qed.

Lemma be_decomposable (ex: Execution) (bound: nat):
  valid_exec ex ->
  numbering_coherent ex ->
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
  intros Hval Hnumco Hbndnotnull.
  rew bounded. apply ext_rel, antisym.
  - kat.
  - rewrite NLE_bound_min_one.
    assert (prefix (bounded_exec ex (bound - 1)) (bounded_exec ex bound)) as Hpre.
    { apply (two_ord_bounds_pre _ _ _ Hval Hnumco). lia. }
    rewrite (rb_prefix_incl Hpre). kat.
Qed.

Ltac solve_trt_bounds := (simpl_trt; auto; unfold NLE; lia).

Lemma be_union_bound_min_one (ex: Execution) (bound: nat) (x y: Event):
  numbering_coherent ex ->
  ((sb (bounded_exec ex bound) ⊔
    rf (bounded_exec ex bound) ⊔
    mo (bounded_exec ex bound) ⊔
    rb (bounded_exec ex bound)) \
   (sb (bounded_exec ex (bound-1)) ⊔
    rf (bounded_exec ex (bound-1)) ⊔
    mo (bounded_exec ex (bound-1)) ⊔
    rb (bounded_exec ex (bound-1)))) x y ->
  (numbering x) = bound \/ (numbering y) = bound.
Proof.
  intros Hnumco [H Hnot].
  destruct (Compare_dec.lt_eq_lt_dec (numbering x) bound) as [[Hordx|Hordx]|Hordx];
  destruct (Compare_dec.lt_eq_lt_dec (numbering y) bound) as [[Hordy|Hordy]|Hordy].
  - exfalso. apply Hnot.
    unfold rb. unfold rb in H. rew bounded. rew bounded in H.
    destruct H as [[[H|H]|H]|H].
    + left; left; left. apply simpl_trt_rel in H. solve_trt_bounds.
    + left; left; right. apply simpl_trt_rel in H. solve_trt_bounds.
    + left; right. apply simpl_trt_rel in H. solve_trt_bounds.
    + right. destruct H as [z Hrf Hmo]. exists z.
      * apply simpl_trt_rel in Hrf. rewrite <- cnv_rev.
        apply (rf_num_ord _ _ _ Hnumco) in Hrf as Hordz. solve_trt_bounds.
      * apply simpl_trt_rel in Hmo. apply simpl_trt_rel in Hrf.
        apply (rf_num_ord _ _ _ Hnumco) in Hrf as Hordz. solve_trt_bounds.
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
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  (numbering k) > (numbering j) ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  (sb (bounded_exec ex bound) ⊔ rf (bounded_exec ex bound) ⊔ 
   mo (bounded_exec ex bound) ⊔ rb (bounded_exec ex bound))^+ k k.
Proof.
  intros Hval Hrc11 Hnumco Hnuminj Hmcp Hord Hnotsc.
  (* inversion Hcomp as [Hval _]. *)
  assert (sc_consistent (bounded_exec ex (bound-1))) as Hsc.
  { eapply smaller_than_smallest_sc; eauto.
    inversion Hmcp as [Hscb _].
    erewrite S_min_one. { auto. }
    eapply mcp_bound_gt_zero; eauto. }
  unfold sc_consistent in *.
  apply not_and_or in Hnotsc as [Hnotat | Hcyc].
  { apply (bounded_is_rc11 _ bound Hval) in Hrc11 as [_ [Hat _]];
    intuition auto. }
  apply not_acyclic_is_cyclic in Hcyc.
  destruct Hsc as [_ Hsc].
  destruct Hcyc as [x Hcyc].
  assert (In _ (evts (bounded_exec ex bound)) x) as Hxevts.
  { eapply tc_sbrfmorb_in_l.
    - apply bounded_is_valid; eauto.
    - eauto.
  }
  rewrite (be_decomposable _ _ Hval Hnumco (mcp_bound_gt_zero _ _ _ _ Hnuminj Hmcp)) in Hcyc.
  pose proof (added_cycle_pass_through_addition _ _ _ Hsc Hcyc) as H.
  destruct H as [z1 [z2 Hbegin Hmid] Hend].
  rewrite <- (be_decomposable _ _ Hval Hnumco (mcp_bound_gt_zero _ _ _ _ Hnuminj Hmcp)) in Hbegin, Hend.
  inversion Hmid as [Hz1z2 _].
  assert (In _ (evts ex) k) as Hkevts.
  { eapply mcp_in_evts_right2; eauto. }
  pose proof (be_union_bound_min_one _ _ _ _ Hnumco Hmid) as [Hz|Hz]; clear Hmid;
  apply (mcp_num_snd_evt _ _ _ _ Hval Hnumco) in Hmcp as Hk;
  rewrite (max_rewrite _ _ Hord) in Hk;
  rewrite <-Hk in Hz;
  rewrite <-(numbering_injective_eq _ _ _ Hnuminj) in Hz; auto.
  - rewrite <-Hz.
    rewrite tc_inv_dcmp2. exists z1. { auto. }
    apply rtc_trans. exists x; auto.
  - rewrite <-Hz. rewrite tc_inv_dcmp. exists z2; auto.
    apply rtc_trans. exists x; auto.
Qed.

Lemma mcp_write_1 (ex: Execution) (bound: nat) (k j: Event):
  valid_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  (numbering k) > (numbering j) ->
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
  intros Hval Hrc11 Hnumco Hnuminj Hmcp Hord Hwk Hnotsc.
  (* inversion Hcomp as [Hval _]. *)
  pose proof (mcp_write_cycle _ _ _ _ Hval Hrc11 Hnumco Hnuminj Hmcp Hord Hnotsc).
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
  - auto.
  - destruct Hrb as [z Hrf _].
    rewrite <-cnv_rev in Hrf.
    eapply rf_dest_read in Hrf.
    + exfalso. destruct k; auto.
    + apply bounded_is_valid; auto.
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
  (numbering y) <= bound.
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
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  (numbering k) > (numbering j) ->
  is_write k ->
  (numbering c) < bound ->
  (* ~(sc_consistent (bounded_exec ex bound)) -> *)
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
  intros Hval Hrc11 Hnumco Hnuminj Hmcp Hord Hw Hc Hck.
  rewrite (be_decomposable _ _ Hval Hnumco (mcp_bound_gt_zero _ _ _ _ Hnuminj Hmcp)) in Hck.
  rewrite tc_union_dcmp in Hck.
  destruct Hck as [Hck|Hck].
  { rewrite tc_inv_dcmp in Hck. destruct Hck as [z _ Hck].
    apply (mcp_num_snd_evt _ _ _ _ Hval Hnumco) in Hmcp.
    rewrite (max_rewrite _ _ Hord) in Hmcp.
    apply sbrfmorb_bound_right in Hck. lia.
  }
  destruct Hck as [w1 [w2 H1 H2] _].
  exists w2. split. auto.
  rewrite rtc_inv_dcmp6 in H1.
  destruct H1 as [H1|H1].
  - simpl in H1. rewrite <-H1 in H2.
    apply (be_union_bound_min_one _ _ _ _ Hnumco) in H2 as Hcw1.
    destruct Hcw1. 
    + lia.
    + apply (mcp_num_snd_evt _ _ _ _ Hval Hnumco) in Hmcp.
      rewrite (max_rewrite _ _ Hord) in Hmcp.
      rewrite <-H in Hmcp. apply (numbering_injective_eq _ _ _ Hnuminj) in Hmcp.
      rewrite Hmcp. rewrite <-H1. destruct H2 as [H2 _].
      rewrite Hmcp in Hw. eapply sbrfmorb_to_write; auto.
      apply bounded_is_valid; auto.
  - apply (be_union_bound_min_one _ _ _ _ Hnumco) in H2 as Hw1w2.
    destruct Hw1w2 as [Hw2|Hw1].
    + rewrite tc_inv_dcmp in H1. destruct H1 as [w3 _ H1].
      apply sbrfmorb_bound_right in H1. lia.
    + apply (mcp_num_snd_evt _ _ _ _ Hval Hnumco) in Hmcp.
      rewrite (max_rewrite _ _ Hord) in Hmcp.
      rewrite <-Hw1 in Hmcp. apply (numbering_injective_eq _ _ _ Hnuminj) in Hmcp.
      rewrite <- Hmcp in H2. apply minus_incl in H2.
      apply sbrfmorb_to_write  in H2; auto.
      apply bounded_is_valid; auto.
Qed.

Lemma mcp_write_not_at (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering y) > (numbering x) ->
  is_write y ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  ~(In _ (At (bounded_exec ex bound)) y).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hxw Hnotsc Hnot.
  inversion Hcomp as [Hval _].
  assert (valid_exec (bounded_exec ex bound)) as Hvalb.
  { apply bounded_is_valid; auto. }
  assert (complete_exec (bounded_exec ex bound)) as Hcompb.
  { apply bounded_is_complete; auto. }
  destruct Hnot as [y [b Hrmw] | y [b Hrmw]].
  - apply (rmw_orig_read _ Hvalb) in Hrmw.
    destruct y; intuition auto.
  - destruct (mcp_write_1 _ _ _ _ Hval Hrc11 Hnumco Hnuminj Hmcp Hord Hxw Hnotsc) as [c [Hyc Hcy]].
    pose proof (mcp_num_snd_evt _ _ _ _ Hval Hnumco Hmcp) as Hybound.
    rewrite (max_rewrite _ _ Hord) in Hybound.

    assert (numbering c < bound) as Hordc.
    { destruct (Compare_dec.lt_eq_lt_dec bound (numbering c)) as [[H'|H']|H'].
      - apply simpl_trt_tright in Hyc. unfold NLE in Hyc. lia.
      - rewrite <-Hybound in H'. apply (numbering_injective_eq _ _ _ Hnuminj) in H'.
        rewrite <-H' in Hyc. exfalso. eapply (mo_irr (bounded_exec ex bound)).
        + apply bounded_is_complete; auto.
        + split. eauto. split.
      - lia.
    }

    eapply (mcp_write_2 _ _ _ _ _ Hval Hrc11 Hnumco Hnuminj Hmcp Hord Hxw Hordc (*Hnotsc*)) 
    in Hcy as [d [Hcd Hdy]].

    inversion Hmcp as [Hscb _].

    assert (numbering b < bound) as Hordb.
    { apply rmw_incl_sb in Hrmw.
      - apply sb_num_ord in Hrmw.
        + lia.
        + eapply numbering_coherent_pre. eauto.
          apply bounded_exec_is_prefix; auto.
      - apply bounded_is_valid; auto.
    }

    unshelve (epose proof (smaller_than_smallest_sc _ _ Hval Hnumco Hrc11 Hscb (bound-1) _) as Hsc).
    { apply (mcp_bound_gt_zero _ _ _ _ Hnuminj) in Hmcp. lia. }

    assert (numbering d < bound) as Hordd.
    { destruct (Compare_dec.lt_eq_lt_dec bound (numbering d)) as [[H'|H']|H'].
      - destruct Hdy as [[Hdy|Hdy]|Hdy].
        + apply simpl_trt_hyp in Hdy as [Hdy _]. unfold NLE in *. lia.
        + apply simpl_trt_hyp in Hdy as [Hdy _]. unfold NLE in *. lia.
        + unfold rb in Hdy. destruct Hdy as [z Hdy _]. rewrite <-cnv_rev in Hdy.
          apply simpl_trt_tright in Hdy. unfold NLE in *. lia.
      - rewrite H' in Hybound. rewrite <-(numbering_injective_eq _ _ _ Hnuminj) in Hybound.
        rewrite Hybound in Hdy. destruct Hdy as [[Hdy|Hdy]|Hdy]; exfalso.
        + eapply ((proj2 (irreflexive_is_irreflexive _)) (sb_irr _ Hvalb)). eauto.
        + eapply ((proj2 (irreflexive_is_irreflexive _)) (mo_irr _ Hvalb)). eauto.
        + eapply ((proj2 (irreflexive_is_irreflexive _)) (rb_irr _ Hvalb)). eauto.
      - lia.
    }
    rewrite <-union_assoc in Hdy. destruct Hdy as [Hdy|Hdy].

    + apply (rmw_incl_imm_sb _ Hvalb) in Hrmw as Himm.
      destruct Himm as [Hr Himm].
      destruct (Himm d Hdy) as [Hdb _].
      assert ((rb (bounded_exec ex (bound-1))) b c) as Hbc.
      { eapply rc11_rmw_incl_rb in Hrmw.
        - destruct Hrmw as [z Hrfinv Hmo].
          assert (numbering z < bound).
          { apply simpl_trt_rel, (rf_num_ord _ _ _ Hnumco) in Hrfinv. lia. }
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
        - apply bounded_is_complete; auto.
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
        - eapply (bounded_is_complete _ (bound-1)).
          + eapply Hcomp.
          + eapply Hnumco.
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
          assert (numbering z < bound).
          { apply rf_num_ord in Hrfinv. lia.
            eapply numbering_coherent_pre. eauto.
            eapply bounded_exec_is_prefix; eauto.
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
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  numbering y > numbering x ->
  In _ (evts (bounded_exec ex bound)) w ->
  w <> y ->
  In _ (evts (bounded_exec ex (bound-1))) w.
Proof.
  intros Hco Hrc11 Hnumco Hnuminj Hmcp Hord Hin Hdiff.
  inversion Hco as [Hval _].
  rewrite simpl_evts_be in *.
  apply in_intersection in Hin as [Hevts Hnumw].
  split; auto.
  unfold In in *.
  destruct (Compare_dec.lt_eq_lt_dec bound (numbering w)) as [[Hord1|Hord1]|Hord1].
  - lia.
  - pose proof (mcp_num_snd_evt _ _ _ _ Hval Hnumco Hmcp) as Hnumy.
    rewrite (max_rewrite _ _ Hord) in Hnumy.
    rewrite Hord1 in Hnumy. apply (numbering_injective_eq _ _ _ Hnuminj) in Hnumy.
    congruence.
  - lia.
Qed.

Lemma mo_change_complete (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering y) > (numbering x) ->
  is_write y ->
  complete_exec (prefix_change_mo ex bound y).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw.
  inversion Hcomp as [Hval _]; inverse_val_exec Hval.
  split;[split;[|split;[|split;[|split]]]|]; rew change_mo.
  - eapply prefix_evts_valid. eauto. apply bounded_exec_is_prefix; auto.
  - eapply prefix_sb_valid. eauto. apply bounded_exec_is_prefix; auto.
  - eapply prefix_rmw_valid_diff_evts.
    + eauto.
    + apply two_ord_bounds_pre; auto. apply mcp_bound_gt_zero in Hmcp. lia. auto.
    + apply bounded_exec_is_prefix; auto.
  - eapply prefix_rf_valid_diff_evts.
    + eauto.
    + apply two_ord_bounds_pre; auto. apply mcp_bound_gt_zero in Hmcp. lia. auto.
    + apply bounded_exec_is_prefix; auto.
  - assert (valid_exec (bounded_exec ex (bound-1))) as Hvalbmin1.
    { eapply bounded_is_valid; auto. }
    assert (valid_exec (bounded_exec ex bound)) as Hvalbmin2.
    { eapply bounded_is_valid; auto. }
    assert (prefix (bounded_exec ex (bound-1)) (bounded_exec ex bound)) as Hpre.
    { eapply two_ord_bounds_pre; auto. apply mcp_bound_gt_zero in Hmcp. lia. auto. }
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
        unfold NLE in H2. rewrite Hmcp in H2. lia. auto.
      * right. intuition auto.
    + intros w1 [Hnot|Hnot].
      * destruct Hvalbmin1 as [_ [_ [_ [_ Hmo_v1]]]].
        destruct Hmo_v1 as [_ [_ [[_ [_ Hmo_v1]] _]]].
        apply (Hmo_v1 w1). auto.
      * destruct Hnot as [Heq [Hin _]].
        rewrite Heq in Hin.
        apply (mcp_num_snd_evt _ _ _ _ Hval) in Hmcp; auto.
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
             apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hin2 Hw2).
          ++ apply (writes_loc_is_write _ _ _ Hin2).
          ++ apply writes_loc_loc in Hin1.
             apply writes_loc_loc in Hin2.
             rewrite <-Hw1, Hin1. auto.
        -- split; eapply writes_loc_loc; eauto.
      * left. split.
        -- right. repeat (apply conj).
           ++ auto.
           ++ apply writes_loc_evts in Hin1.
              apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hin1 Hw1).
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
             ** apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw1evts) in Hw1.
                unfold In in Hw1. rewrite simpl_evts_be in Hw1.
                apply in_intersection in Hw1 as [_ Hw1].
                unfold In in Hw1. unfold NLE. lia.
             ** destruct Hmow1w2. auto.
             ** apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw2evts) in Hw2.
                unfold In in Hw2. rewrite simpl_evts_be in Hw2.
                apply in_intersection in Hw2 as [_ Hw2].
                unfold In in Hw2. unfold NLE. lia.
           ++ apply writes_loc_loc in Hin1. auto.
           ++ apply writes_loc_loc in Hin2. auto.
        -- right. repeat (apply conj).
           ++ left. rew bounded. simpl_trt.
             ** apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw2evts) in Hw2.
                unfold In in Hw2. rewrite simpl_evts_be in Hw2.
                apply in_intersection in Hw2 as [_ Hw2].
                unfold In in Hw2. unfold NLE. lia.
             ** destruct Hmow2w1. auto.
             ** apply (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw1evts) in Hw1.
                unfold In in Hw1. rewrite simpl_evts_be in Hw1.
                apply in_intersection in Hw1 as [_ Hw1].
                unfold In in Hw1. unfold NLE. lia.
           ++ apply writes_loc_loc in Hin2. auto.
           ++ apply writes_loc_loc in Hin1. auto.
  - intros z [Hzevts Hzread].
    assert (z <> y) as Hdiff.
    { destruct (classic (y = z)); auto.
      rewrite H in Hw. destruct z; auto. }
    pose proof (evt_diff_bound _ _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hzevts Hdiff) as Hzb1.
    destruct Hcomp as [_ Hcomp].
    rewrite simpl_evts_be in Hzevts.
    apply in_intersection in Hzevts as [Hzevts _].
    edestruct Hcomp as [w H].
    + split; eauto.
    + exists w. rew bounded.
      rewrite simpl_evts_be in Hzb1.
      apply in_intersection in Hzb1 as [_ Hordz].
      simpl_trt; unfold NLE; unfold In in *.
      * apply rf_num_ord in H. lia. auto.
      * auto.
Qed.

Lemma rf_incl_rf_le (ex: Execution) (b1 b2: nat):
  b1 <= b2 ->
  rf (bounded_exec ex b1) ≦ rf (bounded_exec ex b2).
Proof.
  intros Hord.
  rew bounded.
  apply incl_dot. apply incl_dot; [|auto].
  all: intros x y [Heq Ht]; split; auto; unfold NLE in *; lia.
Qed.

Lemma mo_incl_mo_le (ex: Execution) (b1 b2: nat):
  b1 <= b2 ->
  mo (bounded_exec ex b1) ≦ mo (bounded_exec ex b2).
Proof.
  intros Hord.
  rew bounded.
  apply incl_dot. apply incl_dot; [|auto].
  all: intros x y [Heq Ht]; split; auto; unfold NLE in *; lia.
Qed.

Lemma rmw_incl_rmw_le (ex: Execution) (b1 b2: nat):
  b1 <= b2 ->
  rmw (bounded_exec ex b1) ≦ rmw (bounded_exec ex b2).
Proof.
  intros Hord.
  rew bounded.
  apply incl_dot. apply incl_dot; [|auto].
  all: intros x y [Heq Ht]; split; auto; unfold NLE in *; lia.
Qed.

Lemma sb_incl_sb_le (ex: Execution) (b1 b2: nat):
  b1 <= b2 ->
  sb (bounded_exec ex b1) ≦ sb (bounded_exec ex b2).
Proof.
  intros Hord.
  rew bounded.
  apply incl_dot. apply incl_dot; [|auto].
  all: intros x y [Heq Ht]; split; auto; unfold NLE in *; lia.
Qed.

Lemma rb_incl_rb_le (ex: Execution) (b1 b2: nat):
  b1 <= b2 ->
  rb (bounded_exec ex b1) ≦ rb (bounded_exec ex b2).
Proof.
  intros Hord.
  apply incl_dot.
  - apply cnv_leq_iff. auto using rf_incl_rf_le.
  - auto using mo_incl_mo_le.
Qed.

Lemma rb_incl_change_mo (ex: Execution) (b: nat) (y: Event):
  rb (bounded_exec ex (b-1)) ≦ rb (prefix_change_mo ex b y).
Proof.
  unfold rb.
  rew change_mo.
  kat.
Qed.

Lemma bound_min_one_incl_change_mo (ex: Execution) (bound: nat) (y: Event):
  bound > 0 ->
  (sb (bounded_exec ex (bound-1)) ⊔
   rf (bounded_exec ex (bound-1)) ⊔
   mo (bounded_exec ex (bound-1)) ⊔
   rb (bounded_exec ex (bound-1)))^+ ≦
  (sb (prefix_change_mo ex bound y) ⊔
   rf (prefix_change_mo ex bound y) ⊔
   mo (prefix_change_mo ex bound y) ⊔
   rb (prefix_change_mo ex bound y))^+.
Proof.
  intros Hboundgt0.
  rew change_mo.
  erewrite (sb_incl_sb_le _ (bound-1) bound);[|lia].
  rewrite (rb_incl_change_mo _ _ y). kat.
Qed.


Lemma nothing_after_max_in_change_mo_1 (ex: Execution) (bound: nat) (x y: Event):
  numbering_coherent ex ->
  bound > 0 ->
  numbering x = bound ->
  forall z, ~(sb (prefix_change_mo ex bound y) ⊔
               rf (prefix_change_mo ex bound y) ⊔
               mo (prefix_change_mo ex bound y) ⊔
               rb (prefix_change_mo ex bound y)) x z.
Proof.
  intros Hnumco Hgtzero Hnum z Hnot.
  destruct Hnot as [[[Hend|Hend]|Hend]|Hend].
  - rew change_mo in Hend. rew bounded in Hend.
    apply simpl_trt_tright in Hend as Hordw3.
    apply simpl_trt_rel in Hend.
    apply sb_num_ord in Hend; auto. unfold NLE in *. lia.
  - rew change_mo in Hend. rew bounded in Hend.
    apply simpl_trt_tright in Hend as Hordw3.
    apply simpl_trt_rel in Hend.
    apply rf_num_ord in Hend; auto. unfold NLE in *. lia.
  - rew change_mo in Hend. destruct Hend as [Hend|Hend].
    + rew bounded in Hend. apply simpl_trt_hyp in Hend as [Ht _].
      unfold NLE in *. lia.
    + destruct Hend as [_ [Hend _]]. apply in_intersection in Hend as [_ Hend].
      unfold In in Hend. lia.
  - unfold rb in Hend. rew change_mo in Hend. destruct Hend as [w Hrf _].
    rewrite <-cnv_rev in Hrf. rew bounded in Hrf. apply simpl_trt_tright in Hrf.
    unfold NLE in *. lia.
Qed.

Lemma nothing_after_max_in_change_mo (ex: Execution) (bound: nat) (x y: Event):
  numbering_coherent ex ->
  bound > 0 ->
  numbering x = bound ->
  forall z, ~((sb (bounded_exec ex (bound-1)) ⊔
               rf (bounded_exec ex (bound-1)) ⊔
               mo (bounded_exec ex (bound-1)) ⊔
               rb (bounded_exec ex (bound-1))) ⊔
              (sb (prefix_change_mo ex bound y) ⊔
               rf (prefix_change_mo ex bound y) ⊔
               mo (prefix_change_mo ex bound y) ⊔
               rb (prefix_change_mo ex bound y))) x z.
Proof.
  intros Hnumco Hgtzero Hnum z Hnot.
  destruct Hnot as [[[[Hend|Hend]|Hend]|Hend]|Hend];
  rew bounded in Hend.
  - apply simpl_trt_hyp in Hend as [Ht _].
    unfold NLE in *. lia.
  - apply simpl_trt_hyp in Hend as [Ht _].
    unfold NLE in *. lia.
  - apply simpl_trt_hyp in Hend as [Ht _].
    unfold NLE in *. lia.
  - unfold rb in Hend. destruct Hend as [w4 Hrf _].
    rewrite <-cnv_rev in Hrf. rew bounded in Hrf.
    apply simpl_trt_tright in Hrf. unfold NLE in *. lia.
  - eapply nothing_after_max_in_change_mo_1;
    eauto.
Qed.

Lemma sc_racy_exec (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering y) > (numbering x) ->
  is_write y ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  sc_consistent (prefix_change_mo ex bound y).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw Hnotsc.
  inversion Hcomp as [Hval _].
  unshelve (epose proof (smaller_than_smallest_sc _ bound Hval Hnumco Hrc11 _ (bound-1) _) as Hsc).
  { destruct Hmcp. auto. } 
  { apply mcp_bound_gt_zero in Hmcp. lia. auto. }
  apply conj.
  - destruct Hsc as [Hat _].
    intros w z.
    destruct (Compare_dec.lt_eq_lt_dec (numbering w) bound) as [[Hordw|Hordw]|Hordw];
    destruct (Compare_dec.lt_eq_lt_dec (numbering z) bound) as [[Hordz|Hordz]|Hordz].
    + intros [Hrmw [v1 [v2 Hrfinv Hmo1] Hmo2]]. apply (Hat w z). apply conj.
      { rew change_mo. auto. }
      exists v1.
      { exists v2. 
        - rew change_mo in Hrfinv. auto.
        - destruct Hmo1 as [Hmo1|[Hv1y _]];[auto|].
          apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
          apply (numbering_injective_eq _ _ _ Hnuminj) in Hv1y.
          rewrite Hord in Hv1y.
          destruct Hmo2 as [Hmo2|[_ [Hv1minone _]]].
          + rew bounded in Hmo2. apply simpl_trt_hyp in Hmo2 as [Hv1ord _].
            unfold NLE in Hv1ord. lia.
          + apply in_intersection in Hv1minone as [_ Hv1ord].
            unfold In in Hv1ord. lia.
      }
      destruct Hmo2 as [Hmo2|[Hzy _]];[auto|].
      apply (numbering_injective_eq _ _ _ Hnuminj) in Hzy.
      apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
      rewrite Hord in Hzy. lia.
    + intros [Hrmw _].
      eapply mcp_write_not_at; eauto.
      apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
      rewrite <-Hord in Hordz.
      apply (numbering_injective_eq _ _ _ Hnuminj) in Hordz.
      rewrite Hordz in Hrmw. right. exists w.
      rew change_mo in Hrmw. apply (incl_rel_thm Hrmw).
      apply rmw_incl_rmw_le. lia.
    + intros [_ [v _ Hmo]].
      rew change_mo in Hmo. destruct Hmo as [Hmo|[Hzy _]].
      * rew bounded in Hmo.
        apply simpl_trt_tright in Hmo. unfold NLE in Hmo. lia.
      * apply (numbering_injective_eq _ _ _ Hnuminj) in Hzy.
        apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
        rewrite Hord in Hzy. lia.
    + intros [Hrmw _].
      rew change_mo in Hrmw. rew bounded in Hrmw.
      apply simpl_trt_hyp in Hrmw as [Ht _].
      unfold NLE in *. lia.
    + intros [Hrmw _].
      rew change_mo in Hrmw. rew bounded in Hrmw.
      apply simpl_trt_hyp in Hrmw as [Ht _].
      unfold NLE in *. apply mcp_bound_gt_zero in Hmcp. lia. auto.
    + intros [Hrmw _].
      rew change_mo in Hrmw. rew bounded in Hrmw.
      apply simpl_trt_hyp in Hrmw as [Ht _].
      unfold NLE in *. apply mcp_bound_gt_zero in Hmcp. lia. auto.
    + intros [Hrmw _].
      rew change_mo in Hrmw. rew bounded in Hrmw.
      apply simpl_trt_hyp in Hrmw as [Ht _].
      unfold NLE in *. lia.
    + intros [Hrmw _].
      rew change_mo in Hrmw. rew bounded in Hrmw.
      apply simpl_trt_hyp in Hrmw as [Ht _].
      unfold NLE in *. lia.
    + intros [Hrmw _].
      rew change_mo in Hrmw. rew bounded in Hrmw.
      apply simpl_trt_hyp in Hrmw as [Ht _].
      unfold NLE in *. lia.
  - intros z Hcyc.
    unshelve (epose proof (bound_min_one_incl_change_mo ex bound y _) as Hdec).
    { eapply mcp_bound_gt_zero; eauto. }
    apply incl_as_eq in Hdec.
    rewrite <-Hdec in Hcyc. clear Hdec.
    destruct Hsc as [_ Hac].
    apply incl_tc_union in Hcyc.
    apply (added_cycle_pass_through_addition _ _ _ Hac) in Hcyc.
    destruct Hcyc as [w1 [w2 Hbeg [Hmid Hnotmid]] Hend].
    apply not_or_and in Hnotmid as [Hnotmid Hnotrb].
    apply not_or_and in Hnotmid as [Hnotmid Hnotmo].
    apply not_or_and in Hnotmid as [Hnotsb Hnotrf].
    destruct (Compare_dec.lt_eq_lt_dec (numbering w1) bound) as [[Hordw1|Hordw1]|Hordw1];
    destruct (Compare_dec.lt_eq_lt_dec (numbering w2) bound) as [[Hordw2|Hordw2]|Hordw2].
    + destruct Hmid as [[[Hsb|Hrf]|Hmo]|Hrb].
      * rew change_mo in Hsb. apply Hnotsb.
        apply simpl_trt_rel in Hsb. rew bounded.
        simpl_trt; unfold NLE; try lia. auto.
      * rew change_mo in Hrf. apply Hnotrf.
        apply simpl_trt_rel in Hrf. rew bounded.
        simpl_trt; unfold NLE; try lia. auto.
      * rew change_mo in Hmo. destruct Hmo as [Hmo|[Hw1y _]].
        -- rew bounded in Hmo. apply simpl_trt_rel in Hmo.
           apply Hnotmo. rew bounded. simpl_trt; unfold NLE; try lia. auto.
        -- apply (numbering_injective_eq _ _ _ Hnuminj) in Hw1y.
           apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
           rewrite Hord in Hw1y. lia.
      * unfold rb in Hrb. destruct Hrb as [w3 Hrfinv Hmo].
        apply cnv_rev in Hrfinv as Hrf. clear Hrfinv.
        rew change_mo in Hrf. apply simpl_trt_rel in Hrf.
        rew change_mo in Hmo. destruct Hmo as [Hmo|[Hw1y _]].
        -- rew bounded in Hmo. apply Hnotrb.
           apply (rf_num_ord _ _ _ Hnumco) in Hrf as Hw3ord.
           exists w3.
           ++ rewrite <-cnv_rev. rew bounded. simpl_trt; auto;
              unfold NLE; lia.
           ++ apply simpl_trt_rel in Hmo. rew bounded. simpl_trt; auto;
              unfold NLE; lia.
        -- apply (numbering_injective_eq _ _ _ Hnuminj) in Hw1y.
           apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
           rewrite Hord in Hw1y. lia.
    + destruct Hmid as [[[Hsb|Hrf]|Hmo]|Hrb].
      * rew change_mo in Hsb. rew bounded in Hsb. apply simpl_trt_rel in Hsb.
        apply sb_num_ord in Hsb. lia. auto.
      * rew change_mo in Hrf. rew bounded in Hrf. apply simpl_trt_rel in Hrf.
        apply rf_num_ord in Hrf. lia. auto.
      * rew change_mo in Hmo. destruct Hmo as [Hmo|[Hw1y _]].
        -- rew bounded in Hmo. apply simpl_trt_hyp in Hmo as [Ht _].
           unfold NLE in Ht. lia.
        -- apply (numbering_injective_eq _ _ _ Hnuminj) in Hw1y.
           apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
           lia.
      * unfold rb in Hrb. destruct Hrb as [w3 Hrfinv _].
        rewrite <-cnv_rev in Hrfinv. rew change_mo in Hrfinv.
        rew bounded in Hrfinv. apply simpl_trt_tright in Hrfinv.
        unfold NLE in *. lia.
    + destruct Hmid as [[[Hsb|Hrf]|Hmo]|Hrb].
      * rew change_mo in Hsb. rew bounded in Hsb.
        apply simpl_trt_hyp in Hsb as [Ht _].
        unfold NLE in *. lia.
      * rew change_mo in Hrf. rew bounded in Hrf.
        apply simpl_trt_hyp in Hrf as [Ht _].
        unfold NLE in *. lia.
      * rew change_mo in Hmo. destruct Hmo as [Hmo|[_ [Hmo _]]].
        -- rew bounded in Hmo.
           apply simpl_trt_hyp in Hmo as [Ht _].
           unfold NLE in *. lia.
        -- apply in_intersection in Hmo as [_ Hmo].
           unfold In in Hmo. lia.
      * unfold rb in Hrb. destruct Hrb as [w3 Hinvrf _].
        rewrite <-cnv_rev in Hinvrf. rew change_mo in Hinvrf.
        rew bounded in Hinvrf. apply simpl_trt_tright in Hinvrf.
        unfold NLE in *. lia.
    + rewrite rtc_inv_dcmp6 in Hend.
      rewrite rtc_inv_dcmp6 in Hbeg.
      destruct Hbeg as [Hbeg|Hbeg];
      destruct Hend as [Hend|Hend].
      * simpl in Hbeg, Hend. rewrite <-Hbeg, Hend in Hmid.
        unfold rb in Hmid. rew change_mo in Hmid. rew bounded in Hmid.
        destruct Hmid as [[[Hmid|Hmid]|Hmid]|Hmid].
        -- eapply ((proj2 (irreflexive_is_irreflexive _)) (sb_irr _ Hval)).
           apply simpl_trt_rel in Hmid. eauto.
        -- eapply ((proj2 (irreflexive_is_irreflexive _)) (rf_irr _ Hval)).
           apply simpl_trt_rel in Hmid. eauto.
        -- destruct Hmid as [Hmid|Hmid].
           ++ eapply ((proj2 (irreflexive_is_irreflexive _)) (mo_irr _ Hval)).
              apply simpl_trt_rel in Hmid. eauto.
           ++ destruct Hmid as [Hzy [Hzbmin1 _]].
              apply in_intersection in Hzbmin1 as [_ Hzord].
              unfold In in Hzord. 
              apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
              apply (numbering_injective_eq _ _ _ Hnuminj) in Hzy.
              rewrite Hord in Hzy. lia.
        -- destruct Hmid as [w3 Hrfinv [Hmo|Hmo]].
           ++ eapply ((proj2 (irreflexive_is_irreflexive _)) (rb_irr _ Hval)).
              rewrite 2dot_cnv in Hrfinv. destruct Hrfinv as [w4 [Heq _] [w5 Hrf [Heq2 _]]].
              rewrite <-cnv_rev in Hrf. rewrite Heq, <-Heq2 in Hrf.
              apply simpl_trt_rel in Hmo. exists w3.
              ** rewrite <-cnv_rev. eauto.
              ** eauto.
           ++ destruct Hmo as [Hzy _]. rewrite Hzy in Hbeg.
              apply (numbering_injective_eq _ _ _ Hnuminj) in Hbeg.
              apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
              rewrite Hord in Hbeg. lia.
      * rewrite tc_inv_dcmp2 in Hend. destruct Hend as [w3 Hend _].
        eapply (nothing_after_max_in_change_mo _ bound _ _); eauto.
        eapply mcp_bound_gt_zero; eauto.
      * simpl in Hend. rewrite <-Hend in Hbeg. rewrite tc_inv_dcmp2 in Hbeg.
        destruct Hbeg as [w3 Hbeg _].
        eapply (nothing_after_max_in_change_mo _ bound _ _); eauto.
        eapply mcp_bound_gt_zero; eauto.
      * rewrite tc_inv_dcmp2 in Hend. destruct Hend as [w3 Hend _].
        eapply (nothing_after_max_in_change_mo _ bound _ _); eauto.
        eapply mcp_bound_gt_zero; eauto.
    + eapply (nothing_after_max_in_change_mo_1 _ bound); eauto.
      eapply mcp_bound_gt_zero; eauto.
    + destruct Hmid as [[[Hsb|Hrf]|Hmo]|Hrb].
      * rew change_mo in Hsb. rew bounded in Hsb. apply simpl_trt_rel in Hsb.
        apply sb_num_ord in Hsb. lia. auto.
      * rew change_mo in Hrf. rew bounded in Hrf. apply simpl_trt_rel in Hrf.
        apply rf_num_ord in Hrf. lia. auto.
      * rew change_mo in Hmo. destruct Hmo as [Hmo|[_ [Hw2bmin1 _]]].
        -- rew bounded in Hmo. apply simpl_trt_hyp in Hmo as [Ht _].
           unfold NLE in Ht. lia.
        -- apply in_intersection in Hw2bmin1 as [_ Hw2bmin1].
           unfold In in Hw2bmin1. lia.
      * unfold rb in Hrb. destruct Hrb as [w3 Hrfinv _].
        rewrite <-cnv_rev in Hrfinv. rew change_mo in Hrfinv.
        rew bounded in Hrfinv. apply simpl_trt_tright in Hrfinv.
        unfold NLE in *. lia.
    + destruct Hmid as [[[Hsb|Hrf]|Hmo]|Hrb].
      * rew change_mo in Hsb. rew bounded in Hsb.
        apply simpl_trt_tright in Hsb as Ht.
        unfold NLE in *. lia.
      * rew change_mo in Hrf. rew bounded in Hrf.
        apply simpl_trt_tright in Hrf as Ht.
        unfold NLE in *. lia.
      * rew change_mo in Hmo. destruct Hmo as [Hmo|[Hmo _]].
        -- rew bounded in Hmo.
           apply simpl_trt_tright in Hmo as Ht.
           unfold NLE in *. lia.
        -- apply (numbering_injective_eq _ _ _ Hnuminj) in Hmo.
           apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
           lia.
      * unfold rb in Hrb. destruct Hrb as [w3 _ Hmo].
        rew change_mo in Hmo. destruct Hmo as [Hmo|[Hmo _]].
        -- rew bounded in Hmo.
           apply simpl_trt_tright in Hmo as Ht.
           unfold NLE in *. lia.
        -- apply (numbering_injective_eq _ _ _ Hnuminj) in Hmo.
           apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
           lia.
    + eapply (nothing_after_max_in_change_mo_1 _ bound); eauto.
      eapply mcp_bound_gt_zero; eauto.
    + destruct Hmid as [[[Hsb|Hrf]|Hmo]|Hrb].
      * rew change_mo in Hsb. rew bounded in Hsb.
        apply simpl_trt_tright in Hsb as Ht.
        unfold NLE in *. lia.
      * rew change_mo in Hrf. rew bounded in Hrf.
        apply simpl_trt_tright in Hrf as Ht.
        unfold NLE in *. lia.
      * rew change_mo in Hmo. destruct Hmo as [Hmo|[Hmo _]].
        -- rew bounded in Hmo.
           apply simpl_trt_tright in Hmo as Ht.
           unfold NLE in *. lia.
        -- apply (numbering_injective_eq _ _ _ Hnuminj) in Hmo.
           apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
           lia.
      * unfold rb in Hrb. destruct Hrb as [w3 _ Hmo].
        rew change_mo in Hmo. destruct Hmo as [Hmo|[Hmo _]].
        -- rew bounded in Hmo.
           apply simpl_trt_tright in Hmo as Ht.
           unfold NLE in *. lia.
        -- apply (numbering_injective_eq _ _ _ Hnuminj) in Hmo.
           apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord.
           lia.
Qed.

Lemma write_rf_eq_rfbminone (ex: Execution) (bound: nat) (x: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  numbering x = bound ->
  is_write x ->
  rf (bounded_exec ex bound) = rf (bounded_exec ex (bound-1)).
Proof.
  intros Hval Hnumco Hnuminj Hnum Hw.
  apply ext_rel, antisym.
  - intros y z Hrf. rew bounded. rew bounded in Hrf.
    apply simpl_trt_hyp in Hrf as [Hleft [Hrel Hright]].
    unfold NLE in Hleft, Hright. simpl_trt; auto; unfold NLE;
    apply (rf_num_ord _ _ _ Hnumco) in Hrel as Hyz;
    destruct (Compare_dec.lt_eq_lt_dec (numbering z) bound) as [[Hz|Hz]|Hz];
    try lia.
    rewrite <-Hz in Hnum.
    apply (numbering_injective_eq _ _ _ Hnuminj) in Hnum. rewrite Hnum in Hw.
    apply (rf_dest_read _ Hval) in Hrel.
    destruct z; simpl in *; intuition auto.
  - intros y z Hrf.
    rew bounded in Hrf. rew bounded. apply simpl_trt_hyp in Hrf as [Hleft [Hrel Hright]].
    simpl_trt; unfold NLE in *; auto; lia.
Qed.

Lemma write_rmw_eq_rmwbminone (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  numbering y > numbering x ->
  is_write y ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  rmw (bounded_exec ex bound) = rmw (bounded_exec ex (bound-1)).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw Hnotsc.
  inversion Hcomp as [Hval _].
  pose proof (mcp_write_not_at _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw Hnotsc) as Hnotat.
  apply ext_rel, antisym.
  - intros w z Hrmw. rew bounded. rew bounded in Hrmw.
    apply simpl_trt_hyp in Hrmw as [Hleft [Hrel Hright]].
    apply (rmw_incl_sb _ Hval) in Hrel as Hsb.
    unfold NLE in Hleft, Hright. simpl_trt; auto; unfold NLE;
    apply (sb_num_ord _ _ _ Hnumco) in Hsb;
    destruct (Compare_dec.lt_eq_lt_dec (numbering z) bound) as [[Hz|Hz]|Hz];
    try lia.
    apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp)in Hord.
    rewrite <-Hz in Hord. apply (numbering_injective_eq _ _ _ Hnuminj) in Hord.
    rewrite Hord in Hnotat.
    exfalso. apply Hnotat. right. exists w.
    rew bounded. simpl_trt. auto.
  - intros w z Hrf.
    rew bounded in Hrf. rew bounded. apply simpl_trt_hyp in Hrf as [Hleft [Hrel Hright]].
    simpl_trt; unfold NLE in *; auto; lia.
Qed.

(** If there is a race in an execution, changing the modification order of this
execution maintains the race *)

Lemma race_implies_race_change_mo (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound x y ->
  numbering y > numbering x ->
  is_write y ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  race (bounded_exec ex bound) x y ->
  race (prefix_change_mo ex bound y) x y.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hyw Hnotsc [Hw [Hdiff [Hloc [Hxy Hyx]]]].
  inversion Hcomp as [Hval _].
  repeat (apply conj); auto.
  - clear Hyx.
    intros Hnot. apply Hxy.
    apply (incl_rel_thm Hnot).
    unfold hb. apply tc_incl, union_incl.
    { kat. }
    unfold sw, rs. rew change_mo.
    unshelve (erewrite <-(write_rf_eq_rfbminone _ _ _ Hval Hnumco Hnuminj _ Hyw)).
    { eapply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord). }
    erewrite (write_rmw_eq_rmwbminone _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hyw Hnotsc).
    kat.
  - clear Hxy.
    intros Hnot. apply Hyx.
    apply (incl_rel_thm Hnot).
    unfold hb. apply tc_incl, union_incl.
    { kat. }
    unfold sw, rs. rew change_mo.
    unshelve (erewrite <-(write_rf_eq_rfbminone _ _ _ Hval Hnumco Hnuminj _ Hyw)).
    { eapply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord). }
    erewrite (write_rmw_eq_rmwbminone _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hyw Hnotsc).
    kat.
Qed.

Definition sbrf_before_jk (ex: Execution) (bound: nat) (j k: Event) :=
  fun e => (sb ex ⊔ rf (bounded_exec ex (bound-1)))^* e j \/ 
           (sb ex ⊔ rf (bounded_exec ex (bound-1)))^* e k.

Lemma sbrf_minone_sbrf (ex: Execution) (bound: nat):
  (sb ex ⊔ rf (bounded_exec ex (bound-1))) ≦ (sb ex ⊔ rf ex).
Proof. rew bounded. kat. Qed.

Lemma sbrf_minone_sbrf_rtc (ex: Execution) (bound: nat):
  (sb ex ⊔ rf (bounded_exec ex (bound-1)))^* ≦ (sb ex ⊔ rf ex)^*.
Proof. rew bounded. kat. Qed.

Lemma sbrf_before_jk_num (ex: Execution) (bound: nat) (x j k: Event):
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  In _ (sbrf_before_jk ex bound j k) x ->
  (numbering x < numbering k) \/ x = k.
Proof.
  intros Hnumco Hmcp Hord [Hin|Hin].
  - apply sbrf_minone_sbrf_rtc in Hin.
    left. eapply (numbering_coherent_rtc _ _ _ Hnumco) in Hin. lia.
  - apply sbrf_minone_sbrf_rtc in Hin.
    rewrite rtc_inv_dcmp6 in Hin. destruct Hin as [Hin|Hin].
    + simpl in Hin. right. auto.
    + eapply (numbering_coherent_tc _ _ _ Hnumco) in Hin. lia.
Qed.

Lemma sbrf_before_jk_bounded (ex: Execution) (bound: nat) (j k x: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k -> 
  numbering k > numbering j ->
  In _ (sbrf_before_jk ex bound j k) x ->
  In _ (evts (bounded_exec ex bound)) x.
Proof.
  intros Hval Hnumco Hmcp Hord Hin.
  pose proof (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord) as Hk.
  destruct Hin as [Hin|Hin].
  - apply sbrf_minone_sbrf_rtc in Hin.
    split.
    + eapply rtc_sbrf_in_l; eauto.
      eapply mcp_in_evts_left2; eauto.
    + apply (numbering_coherent_rtc _ _ _ Hnumco) in Hin.
      unfold In. lia.
  - apply sbrf_minone_sbrf_rtc in Hin.
    split.
    + eapply rtc_sbrf_in_l; eauto.
      eapply mcp_in_evts_right2; eauto.
    + apply (numbering_coherent_rtc _ _ _ Hnumco) in Hin.
      unfold In. lia.
Qed.

Lemma sbrf_before_jk_evts (ex: Execution) (bound: nat) (j k x: Event):
  valid_exec ex ->
  minimal_conflicting_pair ex bound j k ->
  In _ (sbrf_before_jk ex bound j k) x ->
  In _ (evts ex) x.
Proof.
  intros Hval Hmcp Hin.
  destruct Hin as [Hin|Hin];
  rewrite rtc_inv_dcmp6 in Hin;
  destruct Hin as [Hin|Hin].
  - simpl in Hin. rewrite Hin. eapply mcp_in_evts_left2. eauto.
  - rewrite rtc_inv_dcmp7 in Hin. destruct Hin as [z Hrel _].
    apply sbrf_minone_sbrf in Hrel as [Hrel|Hrel].
    + eapply sb_orig_evts; eauto.
    + eapply rf_orig_evts; eauto.
  - simpl in Hin. rewrite Hin. eapply mcp_in_evts_right2. eauto.
  - rewrite rtc_inv_dcmp7 in Hin. destruct Hin as [z Hrel _].
    apply sbrf_minone_sbrf in Hrel as [Hrel|Hrel].
    + eapply sb_orig_evts; eauto.
    + eapply rf_orig_evts; eauto.
Qed.

Lemma sbrf_before_jk_sb (ex: Execution) (bound: nat) (j k e1 e2: Event):
  (I (sbrf_before_jk ex bound j k)) e2 ->
  sb ex e1 e2 ->
  (I (sbrf_before_jk ex bound j k)) e1.
Proof.
  intros [Hrel|Hrel] Hsb; [left|right];
  apply rtc_inv_dcmp2; exists e2.
  - incl_rel_kat Hsb.
  - incl_rel_kat Hrel.
  - incl_rel_kat Hsb.
  - incl_rel_kat Hrel.
Qed.

Lemma sbrf_before_jk_rf (ex: Execution) (bound: nat) (j k e1 e2: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  (I (sbrf_before_jk ex bound j k)) e2 ->
  e2 <> k ->
  rf ex e1 e2 ->
  (I (sbrf_before_jk ex bound j k)) e1.
Proof.
  intros Hval Hnumco Hmcp Hord Hin Hdiff Hrel.
  apply (rf_num_ord _ _ _ Hnumco) in Hrel as He1e2ord.
  apply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord as Hnumk.
  apply (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord) in Hin as H.
  destruct H as [H|H]; [|intuition auto].
  rewrite Hnumk in H.
  destruct Hin as [Hin|Hin]; [left|right];
  apply rtc_inv_dcmp2; exists e2; auto.
  - right. rew bounded. simpl_trt; auto; unfold NLE; lia.
  - right. rew bounded. simpl_trt; auto; unfold NLE; lia.
Qed.

(** When we have a smallest conflicting bounding with [j] and [k] the conflicting 
events, and k is a read we can:

1. Restrict the events to those before [j] or [k] in [(sb ⊔ (NLE (k-1);rf;(NLE (k-1))))^*]
2. Add a new rf-edge between an event still in the execution and [k]

This modification preserves the completeness of the execution, and the coherence
and injectivity of the numbering *)

Definition mo_res (ex: Execution) (bound: nat) (j k: Event) :=
  [I (sbrf_before_jk ex bound j k)] ⋅
  mo ex ⋅
  [I (sbrf_before_jk ex bound j k)].

Definition res_chval_k (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val) :=
  let n := Read (numbering k) (get_mode k) l v in
  let evts_int := sbrf_before_jk ex bound j k in
  let sb_int := [I evts_int]⋅sb ex⋅[I evts_int] in
  let rf_int := [I evts_int]⋅rf ex⋅[(I evts_int) ⊓ ((fun x => x <> k): prop_set Event)] in
  In _ evts_int c /\
  is_write c /\
  is_read k /\
  get_val c = Some v /\
  get_loc c = Some l /\
  evts res = Union _  evts_int (id n) /\
  sb res = sb_int ⊔ (fun x y => sb_int x k /\ y = n) /\
  rmw res = [I evts_int]⋅rmw ex⋅[I evts_int]/\
  rf res =  rf_int ⊔ (fun x y => x = c /\ y = n)/\
  mo res = [I evts_int]⋅mo ex⋅[I evts_int].

Ltac destruct_res_chval H :=
  let Hinc := fresh "Hinc" in
  let Hcw := fresh "Hcw" in
  let Hkr := fresh "Hkr" in
  let Hcval := fresh "Hcval" in
  let Hcloc := fresh "Hcloc" in
  let Hevts := fresh "Hevts" in
  let Hsb := fresh "Hsb" in
  let Hrmw := fresh "Hrmw" in
  let Hrf := fresh "Hrf" in
  let Hmo := fresh "Hmo" in
  destruct H as [Hinc [Hcw [Hkr [Hcval [Hcloc [Hevts [Hsb [Hrmw [Hrf Hmo]]]]]]]]].

Ltac inversion_res_chval H :=
  let Hinc := fresh "Hinc" in
  let Hcw := fresh "Hcw" in
  let Hkr := fresh "Hkr" in
  let Hcval := fresh "Hcval" in
  let Hcloc := fresh "Hcloc" in
  let Hevts := fresh "Hevts" in
  let Hsb := fresh "Hsb" in
  let Hrmw := fresh "Hrmw" in
  let Hrf := fresh "Hrf" in
  let Hmo := fresh "Hmo" in
  inversion H as [Hinc [Hcw [Hkr [Hcval [Hcloc [Hevts [Hsb [Hrmw [Hrf Hmo]]]]]]]]].

Lemma res_chval_exists (ex: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  is_write c ->
  is_read k ->
  get_loc c = Some l ->
  get_val c = Some v ->
  In _ (sbrf_before_jk ex bound j k) c ->
  exists res, res_chval_k ex res bound j k c l v.
Proof.
  intros Hcw Hkr Hcloc Hcval Hinc.
  pose (Read (numbering k) (get_mode k) l v) as n;
  pose (sbrf_before_jk ex bound j k) as evts_int;
  pose ([I evts_int]⋅sb ex⋅[I evts_int]) as sb_int;
  pose ([I evts_int]⋅rf ex⋅[(I evts_int) ⊓ ((fun x => x <> k): prop_set Event)]) as rf_int.
  exists (mkex (Union _  evts_int (id n))
               (sb_int ⊔ (fun x y => sb_int x k /\ y = n))
               ([I evts_int]⋅rmw ex⋅[I evts_int])
               (rf_int ⊔ (fun x y => x = c /\ y = n))
               ([I evts_int]⋅mo ex⋅[I evts_int])).
  unfold res_chval_k. intuition auto.
Qed.

Lemma numco_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  numbering_coherent res.
Proof.
  intros Hnumco Hmcp Hord Hres. destruct_res_chval Hres.
  intros x y [Hxy|Hxy];[rewrite Hsb in Hxy|rewrite Hrf in Hxy];
  destruct Hxy as [Hxy|Hxy].
  - apply simpl_trt_rel in Hxy. apply Hnumco. left. auto.
  - destruct Hxy as [Hxk Hy]. rewrite Hy. simpl.
    apply simpl_trt_rel in Hxk. apply Hnumco. left. auto.
  - apply simpl_trt_rel in Hxy. apply Hnumco. right. auto.
  - destruct Hxy as [Hxc Hy]. rewrite Hy. simpl.
    apply (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord) in Hinc.
    destruct Hinc as [Hinc|Hinc].
    + rewrite Hxc. lia.
    + rewrite Hinc in Hcw.
      destruct k; unfold is_write in Hcw; unfold is_read in Hkr; intuition auto.
Qed.

Lemma numinj_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  numbering_injective ex ->
  res_chval_k ex res bound j k c l v ->
  numbering_injective res.
Proof.
  intros Hnuminj Hres. split; apply Hnuminj; auto.
Qed.


Lemma evts_res_sbrf_numbering_jk (ex res: Execution) (bound: nat) (j k c x: Event) (l: Loc) (v: Val):
  numbering_injective ex ->
  res_chval_k ex res bound j k c l v ->
  In _ (evts res) x ->
  In _ (sbrf_before_jk ex bound j k) x.
Proof.
  intros Hnuminj Hres Hin. destruct_res_chval Hres.
  rewrite Hevts in Hin. apply in_union in Hin.
  destruct Hin as [Hin|Hin]; auto.
  unfold In, id in Hin; simpl in Hin.
  apply (eq_num_read Hnuminj) in Hin.
  rewrite Hin. right. apply one_incl_rtc; simpl; auto.
Qed.

Lemma evts_v_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  res_chval_k ex res bound j k c l v ->
  valid_evts (evts res).
Proof.
  intros Hval Hnuminj Hmcp Hres. destruct_res_chval Hres.
  split.
  - inverse_val_exec Hval. destruct Hevts_v as [H _].
    intros e1 e2 Hine1 Hine2. rewrite Hevts in Hine1, Hine2.
    apply in_union in Hine1 as [Hine1|Hine1];
    apply in_union in Hine2 as [Hine2|Hine2].
    + apply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hine1.
      apply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hine2.
      apply H; auto.
    + apply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hine1.
      apply in_id in Hine2.
      pose proof (mcp_in_evts_right2 _ _ _ _ Hmcp) as Hink.
      specialize (H _ _ Hine1 Hink). destruct H as [H|H].
      * left. rewrite <-Hine2. simpl. apply H.
      * eapply (eq_num_read Hnuminj) in Hine2. right. congruence.
    + apply in_id in Hine1.
      apply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hine2.
      pose proof (mcp_in_evts_right2 _ _ _ _ Hmcp) as Hink.
      specialize (H _ _ Hine2 Hink). destruct H as [H|H].
      * left. rewrite <-Hine1. simpl. intros ?. auto.
      * eapply (eq_num_read Hnuminj) in Hine1. right. congruence.
    + apply in_id in Hine1. apply in_id in Hine2.
      right. eapply (numbering_injective_eq _ _ _ Hnuminj).
      rewrite <-Hine1, <-Hine2. congruence.
  - inverse_val_exec Hval. destruct Hevts_v as [_ H].
    intros e Hin. rewrite Hevts in Hin.
    apply in_union in Hin as [Hin|Hin].
    + apply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hin.
      apply H. auto.
    + apply in_id in Hin. rewrite <-Hin. simpl.
      pose proof (mcp_in_evts_right2 _ _ _ _ Hmcp) as Hink.
      apply H in Hink. destruct k; auto;
      unfold is_read in Hkr; intuition auto.
Qed.

Lemma sb_po_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  partial_order (sb ex) (evts ex) ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c l v ->
  partial_order (sb res) (evts res).
Proof.
  intros [Hsbin [Hsbt Hsbirr]] Hnuminj Hres.
  destruct_res_chval Hres.
  split;[|split].
  - rewrite Hevts, Hsb. apply ext_rel, antisym.
    + intros x y [H|[H Heq]].
      * rewrite test_i_union. incl_rel_kat H.
      * { exists y.
          - exists x.
            + split; auto. left. apply simpl_trt_tleft in H. auto.
            + right; split; auto.
          - split. auto. right. rewrite Heq. unfold In, id. simpl. auto.
        }
    + intros x y H. incl_rel_kat H.
  - intros x y [z Hsb1 Hsb2]. rewrite Hsb in Hsb1, Hsb2. rewrite Hsb.
    destruct Hsb1 as [Hsb1|[Hsb1 Heq1]]; destruct Hsb2 as [Hsb2|[Hsb2 Heq2]].
    + left. simpl_trt.
      * apply simpl_trt_tleft in Hsb1. auto.
      * apply simpl_trt_rel in Hsb1. apply simpl_trt_rel in Hsb2.
        apply Hsbt. exists z; auto.
      * apply simpl_trt_tright in Hsb2. auto.
    + right. split; auto. simpl_trt.
      * apply simpl_trt_tleft in Hsb1. auto.
      * apply simpl_trt_rel in Hsb1. apply simpl_trt_rel in Hsb2.
        apply Hsbt. exists z; auto.
      * apply simpl_trt_tright in Hsb2. auto.
    + apply (eq_num_read2 Hnuminj) in Heq1 as Hzk.
      rewrite <-Hzk in Hsb1 at 3. left. simpl_trt.
      * apply simpl_trt_tleft in Hsb1. auto.
      * apply simpl_trt_rel in Hsb1. apply simpl_trt_rel in Hsb2.
        apply Hsbt. exists z; auto.
      * apply simpl_trt_tright in Hsb2. auto.
    + apply (eq_num_read2 Hnuminj) in Heq2 as Hyk.
      rewrite <-Hyk in Hsb1 at 3. left. auto.
  - intros x H. rewrite Hsb in H. destruct H as [H|[H Heq]].
    + eapply Hsbirr. eapply simpl_trt_rel. eauto.
    + apply (eq_num_read2 Hnuminj) in Heq as Hxk.
      rewrite Hxk in H. eapply Hsbirr. eapply simpl_trt_rel. eauto.
Qed.

Lemma sb_tot_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  total_rel (sb ex) (evts ex) ->
  res_chval_k ex res bound j k c l v ->
  total_rel (sb res) (evts res).
Proof.
  intros Hval Hnumco Hnuminj Hmcp Hord Htot Hres x y Hdiff Hinx Hiny.
  destruct_res_chval Hres. rewrite Hevts in Hinx, Hiny.
  apply in_union in Hinx as [Hinx|Hinx];
  apply in_union in Hiny as [Hiny|Hiny].
  - eapply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hinx as Hinx2.
    eapply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hiny as Hiny2.
    destruct (Htot _ _ Hdiff Hinx2 Hiny2) as [H|H].
    + left. rewrite Hsb. left. simpl_trt. auto.
    + right. rewrite Hsb. left. simpl_trt. auto.
  - eapply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hinx as Hinx2.
    eapply (mcp_in_evts_right2 _ _ _ _) in Hmcp as Hxevts.
    apply in_id in Hiny.
    apply (eq_num_read Hnuminj) in Hiny as Hyk.
    rewrite Hyk in Hdiff.
    destruct (Htot _ _ Hdiff Hinx2 Hxevts).
    + left. rewrite Hsb. right. split; auto. simpl_trt. 
      * auto.
      * unfold sbrf_before_jk. right. apply one_incl_rtc; simpl; auto.
    + apply (sb_num_ord _ _ _ Hnumco) in H.
      destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hinx) as [H'|H'].
      * lia.
      * destruct Hdiff. auto.
  - eapply (sbrf_before_jk_evts _ _ _ _ _ Hval Hmcp) in Hiny as Hiny2.
    eapply (mcp_in_evts_right2 _ _ _ _) in Hmcp as Hxevts.
    apply in_id in Hinx.
    apply (eq_num_read Hnuminj) in Hinx as Hxk.
    rewrite Hxk in Hdiff. apply diff_inv in Hdiff.
    destruct (Htot _ _ Hdiff Hiny2 Hxevts).
    + right. rewrite Hsb. right. split; auto. simpl_trt. 
      * auto.
      * unfold sbrf_before_jk. right. apply one_incl_rtc; simpl; auto.
    + apply (sb_num_ord _ _ _ Hnumco) in H.
      destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hiny) as [H'|H'].
      * lia.
      * destruct Hdiff. auto.
  - eapply Hnuminj in Hdiff.
    apply in_id in Hinx. apply in_id in Hiny.
    rewrite <-Hinx, <-Hiny in Hdiff. simpl in Hdiff. intuition auto.
Qed.

Lemma sb_lso_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  linear_strict_order (sb ex) (evts ex) ->
  res_chval_k ex res bound j k c l v ->
  linear_strict_order (sb res) (evts res).
Proof.
  intros Hval Hnumco Hnuminj Hmcp Hord [Hpo Htot] Hres. apply conj.
  - eapply sb_po_res_chval; eauto.
  - eapply sb_tot_res_chval; eauto.
Qed.

Lemma sb_v_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  valid_sb (evts res) (sb res).
Proof.
  intros Hval Hnumco Hnuminj Hmcp Hord Hres.
  inversion Hval as [_ [Hsb_v _]].
  inversion_res_chval Hres.
  destruct Hsb_v as [Hlso Hsbinit]. split.
  - eapply sb_lso_res_chval; eauto.
  - intros l2. destruct (Hsbinit l2) as [e [H1 [H2 [H3 H4]]]]. exists e.
    split;[|split;[|split]]; auto.
    + intros Hnot. apply H3. rewrite Hsb in Hnot.
      destruct Hnot as [z [Hrel|[Hrel Heq]]].
      * exists z. apply simpl_trt_rel in Hrel. auto.
      * apply (eq_num_read2 Hnuminj) in Heq as Hek.
        rewrite <-Hek in Hrel. exists z. apply simpl_trt_rel in Hrel.
        auto.
    + intros e' Hran. destruct Hran as [z Hran]. rewrite Hsb in Hran.
      destruct Hran as [Hran|[Hran Heq]].
      * assert (sb ex e e').
        { apply H4. exists z. eapply simpl_trt_rel. eauto. }
        rewrite Hsb. left. 
        { simpl_trt.
          - eapply sbrf_before_jk_sb; [|eauto].
            eapply simpl_trt_tright. eauto.
          - auto.
          - eapply simpl_trt_tright. eauto. }
      * apply (eq_num_read2 Hnuminj) in Heq as He'k.
        assert (sb ex e e').
        { apply H4. exists z. rewrite <-He'k in Hran at 3. eapply simpl_trt_rel. eauto. }
        rewrite Hsb. right. split; auto. 
        { simpl_trt.
          - eapply sbrf_before_jk_sb. rewrite <-He'k in Hran at 3. 
            eapply simpl_trt_tright. eauto. auto.
          - rewrite <-He'k. eapply H4. rewrite He'k. exists z. 
            eapply simpl_trt_rel. eauto.
          - right. eapply one_incl_rtc. simpl; auto. }
Qed.

Lemma imm_sb_res_chval (ex res: Execution) (bound: nat) (j k c r w: Event) (l: Loc) (v: Val):
  imm (sb ex) r w ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c l v ->
  (I (sbrf_before_jk ex bound j k)) r ->
  (I (sbrf_before_jk ex bound j k)) w ->
  imm (sb res) r w.
Proof.
  intros [Hrw Himm] Hnuminj Hres Hr Hw. destruct_res_chval Hres.
  split.
  - rewrite Hsb. left. simpl_trt. auto.
  - intros d Hdw. rewrite Hsb in Hdw.
    destruct Hdw as [Hdw|[Hdw Heq]].
    + assert (I (sbrf_before_jk ex bound j k) d) as Hd.
      { eapply sbrf_before_jk_sb; eauto.
        eapply simpl_trt_rel; eauto. }
      apply simpl_trt_rel in Hdw as Hrel.
      apply Himm in Hrel as [H1 H2]. split.
      * { destruct H1 as [H1|H1].
          - left. rewrite Hsb. left. simpl_trt. auto.
          - right. auto. }
      * intros g Hrg. rewrite Hsb in Hrg.
        { destruct Hrg as [Hrg|[Hrk Heq]].
          - apply simpl_trt_hyp in Hrg as [Hleft [Hrel Hright]].
            generalize (H2 _ Hrel). intros H3.
            destruct H3 as [H3|H3].
            + left. rewrite Hsb. left. simpl_trt. auto.
            + right. auto.
          - apply (eq_num_read2 Hnuminj) in Heq as Hgk.
            rewrite Hgk.
            apply simpl_trt_hyp in Hrk as [Hleft [Hrel Hright]].
            generalize (H2 _ Hrel). intros H3.
            destruct H3 as [H3|H3].
            + left. rewrite Hsb. left. simpl_trt. auto.
            + right. auto.
        }
    + apply (eq_num_read2 Hnuminj) in Heq as Hwk.
      split.
      * apply simpl_trt_hyp in Hdw as [Hleft [Hrel Hright]].
        rewrite <-Hwk in Hrel.
        apply Himm in Hrel as [H1 _].
        { destruct H1 as [H1|H1].
          - left. rewrite Hsb. left. simpl_trt. auto.
          - right. auto. }
      * intros g Hrg. rewrite <-Hwk in Hdw at 3.
        apply simpl_trt_hyp in Hdw as [Hleft [Hrel Hright]].
        apply Himm in Hrel as [_ H2].
        rewrite Hsb in Hrg.
        { destruct Hrg as [Hrg|[Hrg Heq2]].
          - apply simpl_trt_hyp in Hrg as [H3 [H4 H5]].
            generalize (H2 _ H4). intros H6.
            destruct H6 as [H6|H6].
            + left. rewrite Hsb. left. simpl_trt. auto.
            + right. auto.
          - apply (eq_num_read2 Hnuminj) in Heq2 as Hgk.
            rewrite Hgk.
            apply simpl_trt_hyp in Hrg as [Hleft2 [Hrel2 Hright2]].
            generalize (H2 _ Hrel2). intros H7.
            destruct H7 as [H7|H7].
            + left. rewrite Hsb. left. simpl_trt. auto.
            + right. auto.
        }
Qed.

Lemma rmw_v1_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c l v ->
  (forall r w, (rmw res) r w -> valid_rmw_pair (sb res) r w).
Proof.
  intros Hval Hnuminj Hres r w Hrel.
  destruct_val_exec Hval. destruct_rmw_v Hrmw_v.
  inversion_res_chval Hres. rewrite Hrmw in Hrel.
  apply simpl_trt_rel in Hrel as Hrw.
  apply Hrmw_vpairs in Hrw. unfold valid_rmw_pair in *.
  destruct (get_mode r); destruct (get_mode w); intuition auto;
  apply simpl_trt_hyp in Hrel as [? [? ?]];
  eapply imm_sb_res_chval; eauto.
Qed.

Lemma rmw_v2_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c l v ->
  rmw res =  [I (evts res)]⋅rmw res⋅[I (evts res)].
Proof.
  intros Hval Hres. destruct_val_exec Hval. destruct_rmw_v Hrmw_v.
  destruct_res_chval Hres.
  rewrite Hevts, Hrmw. rewrite test_i_union. kat_eq.
Qed.

Lemma rmw_v_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c l v ->
  valid_rmw (evts res) (sb res) (rmw res).
Proof.
  intros Hval Hres.
  split.
  - eapply rmw_v1_res_chval; eauto.
  - eapply rmw_v2_res_chval; eauto.
Qed.

Lemma rf_v1_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c l v ->
  (forall w r : Event, rf res w r -> get_loc w = get_loc r /\ get_val w = get_val r).
Proof.
  intros Hval Hres w r Hwr. destruct_val_exec Hval. destruct_rf_v Hrf_v.
  destruct_res_chval Hres. rewrite Hrf in Hwr.
  destruct Hwr as [Hwr|[Hwr Heq]].
  - apply Hrfco. eapply simpl_trt_rel; eauto.
  - rewrite Hwr, Heq. split; auto.
Qed.

Lemma rf_v2_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c l v ->
  rf res = [I (evts res)]⋅rf res⋅[I (evts res)].
Proof.
  intros Hval Hres. destruct_res_chval Hres.
  rewrite Hrf, Hevts.
  apply ext_rel, antisym.
  - intros x y [H|[H1 H2]]; simpl_trt.
    + left. eapply simpl_trt_tleft; eauto.
    + left. auto.
    + left. eapply simpl_trt_tright in H as [H _]. auto.
    + left. rewrite H1. auto.
    + right. auto.
    + right. unfold In, id. simpl. auto.
  - kat.
Qed.

Lemma rf_res_chval_wr (c k: Event) (l: Loc) (v: Val):
  is_write c ->
  (fun x y : Event => x = c /\ y = Read (numbering k) (get_mode k) l v) =
  [W]⋅(fun x y : Event => x = c /\ y = Read (numbering k) (get_mode k) l v)⋅[R].
Proof.
  intros Hcw.
  apply ext_rel, antisym.
  - intros x y [H1 H2]. simpl_trt.
    + rewrite H1. auto.
    + intuition auto.
    + rewrite H2. unfold R. simpl. auto.
  - kat.
Qed.

Lemma rf_v3_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c l v ->
  [W]⋅rf res⋅[R] = rf res.
Proof.
  intros Hval Hres. destruct_res_chval Hres. destruct_val_exec Hval.
  destruct_rf_v Hrf_v.
  rewrite Hrf. rewrite <-Hrfwr at 2. rewrite (rf_res_chval_wr _ _ _ _ Hcw).
  kat_eq.
Qed.

Lemma rf_v4_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c l v ->
  (forall w1 w2 r : Event, rf res w1 r /\ rf res w2 r -> w1 = w2).
Proof.
  intros Hval Hnuminj Hres w1 w2 r [Hw1r Hw2r].
  destruct_res_chval Hres. rewrite Hrf in Hw1r, Hw2r.
  destruct_val_exec Hval. destruct_rf_v Hrf_v.
  destruct Hw1r as [Hw1r|[Hw1r Heq1]]; destruct Hw2r as [Hw2r|[Hw2r Heq2]].
  - apply simpl_trt_rel in Hw1r. apply simpl_trt_rel in Hw2r.
    eapply Hrfun; eauto.
  - eapply simpl_trt_tright in Hw1r as [_ Hcontr].
    eapply (eq_num_read2 Hnuminj) in Heq2. intuition auto.
  - eapply simpl_trt_tright in Hw2r as [_ Hcontr].
    eapply (eq_num_read2 Hnuminj) in Heq1. intuition auto.
  - rewrite Hw1r, Hw2r. auto.
Qed.

Lemma rf_v_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c l v ->
  valid_rf (evts res) (rf res).
Proof.
  intros Hval Hnuminj Hres. split;[|split;[|split]].
  - eapply rf_v1_res_chval; eauto.
  - eapply rf_v2_res_chval; eauto.
  - eapply rf_v3_res_chval; eauto.
  - eapply rf_v4_res_chval; eauto.
Qed.

Lemma mo_v1_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c l v ->
  [W]⋅(mo res)⋅[W] = (mo res).
Proof.
  intros Hval Hres. destruct_res_chval Hres.
  rewrite Hmo. destruct_val_exec Hval. destruct_mo_v Hmo_v.
  rewrite <-Hmoww. kat_eq.
Qed.

Lemma mo_v2_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c l v ->
  (forall x y, (mo res) x y -> get_loc x = get_loc y).
Proof.
  intros Hval Hres x y Hrel.
  destruct_val_exec Hval. destruct_mo_v Hmo_v.
  apply Hmosameloc. destruct_res_chval Hres.
  rewrite Hmo in Hrel. eapply simpl_trt_rel. eauto.
Qed.

Lemma mo_v3_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c l v ->
  partial_order (mo res) (evts res).
Proof.
  intros Hval Hres. destruct_val_exec Hval. destruct_mo_v Hmo_v.
  destruct Hmopo as [Hin [Htrans Hirr]].
  destruct_res_chval Hres.
  split; [|split].
  - rewrite Hmo, Hevts. rewrite I_union. kat_eq.
  - rewrite Hmo. rewrite <-Htrans at 3. kat.
  - intros x Hrel. rewrite Hmo in Hrel. apply simpl_trt_rel in Hrel.
    apply (Hirr x). auto.
Qed.

Lemma writes_loc_res_chval (ex res: Execution) (bound: nat) (j k c x: Event) (l l2: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  res_chval_k ex res bound j k c l v ->
  In _ (writes_loc (evts res) l2) x ->
  In _ (writes_loc (evts ex) l2) x.
Proof.
  intros Hval Hnuminj Hmcp Hres [Hin ?].
  split; auto.
  destruct_res_chval Hres.
  rewrite Hevts in Hin. apply in_union in Hin.
  destruct Hin as [Hin|Hin].
  - eapply sbrf_before_jk_evts; eauto.
  - unfold In, id in Hin. simpl in Hin.
    apply (eq_num_read Hnuminj) in Hin. rewrite Hin.
    eapply mcp_in_evts_right2; eauto.
Qed.

Lemma mo_v4_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  res_chval_k ex res bound j k c l v ->
  (forall l : Loc, total_rel (mo_for_loc (mo res) l) (writes_loc (evts res) l)).
Proof.
  intros Hval Hnuminj Hmcp Hres l2 x y Hdiff Hin1 Hin2.
  eapply writes_loc_res_chval in Hin1 as Hin12; eauto.
  eapply writes_loc_res_chval in Hin2 as Hin22; eauto.
  destruct_val_exec Hval. destruct_mo_v Hmo_v.
  specialize (Hmotot l2 x y Hdiff Hin12 Hin22).
  destruct Hin1 as [Hin1 _]. destruct Hin2 as [Hin2].
  eapply evts_res_sbrf_numbering_jk in Hin1; eauto.
  eapply evts_res_sbrf_numbering_jk in Hin2; eauto.
  destruct_res_chval Hres.
  destruct Hmotot as [[Hmotot ?]|[Hmotot ?]]; [left|right].
  - split; auto. rewrite Hmo. simpl_trt. auto.
  - split; auto. rewrite Hmo. simpl_trt. auto.
Qed.

Lemma mo_v_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  res_chval_k ex res bound j k c l v ->
  valid_mo (evts res) (mo res).
Proof.
  intros Hval Hnuminj Hmcp Hres.
  split;[|split;[|split]].
  - eapply mo_v1_res_chval; eauto.
  - eapply mo_v2_res_chval; eauto.
  - eapply mo_v3_res_chval; eauto.
  - eapply mo_v4_res_chval; eauto.
Qed.

Lemma valid_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  valid_exec res.
Proof.
  intros Hval Hnumco Hnuminj Hmcp Hord Hres.
  split;[|split;[|split;[|split]]].
  - eapply evts_v_res_chval; eauto.
  - eapply sb_v_res_chval; eauto.
  - eapply rmw_v_res_chval; eauto.
  - eapply rf_v_res_chval; eauto.
  - eapply mo_v_res_chval; eauto.
Qed.

Lemma reads_in_rf_ran_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  Included Event (reads (evts res)) (ran (rf res)).
Proof.
  intros [Hval Hcomp] Hnumco Hnuminj Hmcp Hord Hres x [Hin Hread].
  destruct_res_chval Hres.
  rewrite Hevts in Hin.
  apply in_union in Hin as [Hin|Hin];
  destruct (classic (x = k)) as [Hxk|Hxk].
  - exists c. rewrite Hrf. right. split; auto.
    rewrite Hxk. apply (numbering_injective_eq _ _ _  Hnuminj).
    simpl; auto.
  - assert (In _ (ran (rf ex)) x) as H.
    { apply Hcomp. split; auto. eapply sbrf_before_jk_evts; eauto. }
    destruct H as [y H].
    exists y. rewrite Hrf. left. simpl_trt; auto. 
    + eapply sbrf_before_jk_rf; eauto.
    + split; auto.
  - exists c. rewrite Hrf. right. split; auto.
  - exists c. rewrite Hrf. right. split; auto.
Qed.

Lemma complete_res_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  complete_exec res.
Proof.
  intros Hcomp Hnumco Hnuminj Hmcp Hord Hres.
  inversion Hcomp as [Hval Hrfran].
  split.
  - eapply valid_res_chval; eauto.
  - eapply reads_in_rf_ran_res_chval; eauto.
Qed.

(** Last write in the modification order for a given location *)

Definition max_mo_for_loc (e: Event) (evts: Ensemble Event) (mo: rlt Event) (l: Loc) :=
  In _ (writes evts) e /\
  get_loc e = Some l /\
  forall x, In _ (writes evts) x ->
            get_loc x = Some l ->
            x <> e ->
            mo x e.

(** If the execution contains at least one write event to a location l, there 
exists at least on event that is the maximal element in the mo on this location l *)

Axiom exists_max_mo_for_loc:
  forall evts r l,
  r <> empty ->
  exists e, max_mo_for_loc e evts r l.

Lemma change_val_atomicity (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  atomicity res.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hres.
  inversion Hcomp as [Hval _].
  destruct Hrc11 as [_ [Hato _]]. destruct_res_chval Hres.
  intros x y [Hrel1 Hrel2]. rewrite Hrmw in Hrel1.
  unfold rb in Hrel2. rewrite Hrf, Hmo in Hrel2.
  destruct Hrel2 as [z1 [z2 [H1|[Heq1 H1]] H2] H3].
  - apply (Hato x y). split.
    + eapply simpl_trt_rel; eauto.
    + exists z1.
      * exists z2.
        -- rewrite <-cnv_rev. eapply simpl_trt_rel; eauto.
        -- eapply simpl_trt_rel; eauto.
      * eapply simpl_trt_rel; eauto.
  - apply simpl_trt_rel in Hrel1.
    apply (rmw_num_ord _ _ _ Hval Hnumco) in Hrel1 as Hordnot.
    rewrite H1 in Hordnot. simpl in Hordnot.
    apply simpl_trt_tright in H3 as Hiny. unfold I in Hiny.
    apply (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord) in Hiny as [Hiny|Hiny].
    + lia.
    + rewrite Hiny in Hordnot. lia.
Qed.

Lemma max_mo_has_predecessor (ex: Execution) (bound: nat) (j k c: Event) (l: Loc):
  minimal_conflicting_pair ex bound j k ->
  max_mo_for_loc c (sbrf_before_jk ex bound j k) (mo_res ex bound j k) l ->
  c = j ->
  exists d, get_loc d = Some l /\
            (imm (mo ex)) d c.
Proof.
  intros Hmcp Hmaxmo Heq.
  (*
    We know that mo cannot be empty (it would make the execution SC)
    
  *)
Admitted.

Lemma b_res_chval_pre_b (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  prefix (bounded_exec res (numbering k - 1)) (bounded_exec ex (numbering k - 1)).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hres.
  inversion Hcomp as [Hval _].
  inversion_res_chval Hres.
  split;[|split;[|split;[|split;[|split]]]].
  - intros x Hin. apply in_intersection in Hin as [Hin Hinbound].
    split; auto.
    eapply sbrf_before_jk_evts; eauto. 
    eapply evts_res_sbrf_numbering_jk; eauto.
  - intros x y [Hxy|Hxy] Hiny.
    + apply in_intersection in Hiny as [Hiny Hinybound].
      apply simpl_trt_tleft in Hxy as Hnumx.
      split; auto.
      rewrite Hevts. left.
      eapply sbrf_before_jk_sb.
      * eapply evts_res_sbrf_numbering_jk; eauto.
      * rew bounded in Hxy. apply simpl_trt_rel in Hxy. auto.
    + apply in_intersection in Hiny as [Hiny Hinybound].
      apply simpl_trt_tleft in Hxy as Hnumx.
      split; auto.
      rewrite Hevts. left.
      eapply sbrf_before_jk_rf; auto.
      * eapply evts_res_sbrf_numbering_jk; eauto.
      * rew bounded in Hxy. apply simpl_trt_tright in Hxy.
        apply Hnuminj. intros Heq. unfold NLE in Hxy. lia.
      * rew bounded in Hxy. apply simpl_trt_rel in Hxy. auto.
  - apply ext_rel, antisym.
    + intros x y Hxy. rew bounded in Hxy.
      apply simpl_trt_hyp in Hxy as [Hxb [Hxy Hyb]].
      rewrite Hsb in Hxy. simpl_trt.
      * split; auto. destruct Hxy as [Hxy|Hxy].
        -- apply simpl_trt_tleft in Hxy. rewrite Hevts. left. auto.
        -- destruct Hxy as [Hxy _]. apply simpl_trt_tleft in Hxy.
           rewrite Hevts. left. auto.
      * rew bounded. simpl_trt; auto.
        destruct Hxy as [Hxy|Hxy].
        -- apply simpl_trt_rel in Hxy. auto.
        -- destruct Hxy as [_ Hxy]. eapply eq_num_read2 in Hxy; auto.
           unfold NLE in Hyb. eapply numbering_injective_eq in Hxy; auto. lia.
      * split; auto. destruct Hxy as [Hxy|Hxy].
        -- apply simpl_trt_tright in Hxy. rewrite Hevts. left. auto.
        -- destruct Hxy as [_ Hxy]. eapply eq_num_read2 in Hxy; auto.
           unfold NLE in Hyb. eapply numbering_injective_eq in Hxy; auto. lia.
    + intros x y Hxy. apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
      apply in_intersection in Hx as [Hx Hxnum].
      apply in_intersection in Hy as [Hy Hynum].
      rew bounded. simpl_trt; auto.
      rewrite Hsb. left. simpl_trt.
      * eapply evts_res_sbrf_numbering_jk; eauto.
      * rew bounded in Hxy. incl_rel_kat Hxy.
      * eapply evts_res_sbrf_numbering_jk; eauto.
  - apply ext_rel, antisym.
    + intros x y Hxy. rew bounded in Hxy.
      apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
      rewrite Hrf in Hxy. simpl_trt.
      * split; auto. destruct Hxy as [Hxy|Hxy].
        -- apply simpl_trt_tleft in Hxy. rewrite Hevts. left. auto.
        -- destruct Hxy as [Hxc _]. rewrite Hxc, Hevts. left. auto.
      * rew bounded. simpl_trt; auto. destruct Hxy as [Hxy|Hxy].
        -- incl_rel_kat Hxy.
        -- destruct Hxy as [_ Hxy]. eapply eq_num_read2 in Hxy; auto.
           unfold NLE in Hy. eapply numbering_injective_eq in Hxy; auto. lia.
      * split; auto. destruct Hxy as [Hxy|Hxy].
        -- apply simpl_trt_tright in Hxy as [Hxy _]. rewrite Hevts. left. auto.
        -- destruct Hxy as [_ Hxy]. eapply eq_num_read2 in Hxy; auto.
           unfold NLE in Hy. eapply numbering_injective_eq in Hxy; auto. lia.
    + intros x y Hxy. apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
      apply in_intersection in Hx as [Hx Hxnum].
      apply in_intersection in Hy as [Hy Hynum].
      rew bounded. simpl_trt; auto.
      rewrite Hrf. left. simpl_trt.
      * eapply evts_res_sbrf_numbering_jk; eauto.
      * rew bounded in Hxy. incl_rel_kat Hxy.
      * split. { eapply evts_res_sbrf_numbering_jk; eauto. }
        unfold In in Hynum. eapply Hnuminj. lia.
  - apply ext_rel, antisym.
    + intros x y Hxy. 
      rew bounded in Hxy. apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
      rewrite Hmo in Hxy. apply simpl_trt_hyp in Hxy as [Hx2 [Hxy Hy2]].
      simpl_trt.
      * split; auto. rewrite Hevts. left. auto.
      * rew bounded. simpl_trt; auto.
      * split; auto. rewrite Hevts. left. auto.
    + intros x y Hxy. apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
      apply in_intersection in Hx as [Hx Hxnum].
      apply in_intersection in Hy as [Hy Hynum].
      rew bounded; simpl_trt; auto. rewrite Hmo. simpl_trt.
      * eapply evts_res_sbrf_numbering_jk; eauto.
      * rew bounded in Hxy. incl_rel_kat Hxy.
      * eapply evts_res_sbrf_numbering_jk; eauto.
  - apply ext_rel, antisym.
    + intros x y Hxy. 
      rew bounded in Hxy. apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
      rewrite Hrmw in Hxy. apply simpl_trt_hyp in Hxy as [Hx2 [Hxy Hy2]].
      simpl_trt.
      * split; auto. rewrite Hevts. left. auto.
      * rew bounded. simpl_trt; auto.
      * split; auto. rewrite Hevts. left. auto.
    + intros x y Hxy. apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
      apply in_intersection in Hx as [Hx Hxnum].
      apply in_intersection in Hy as [Hy Hynum].
      rew bounded; simpl_trt; auto. rewrite Hrmw. simpl_trt.
      * eapply evts_res_sbrf_numbering_jk; eauto.
      * rew bounded in Hxy. incl_rel_kat Hxy.
      * eapply evts_res_sbrf_numbering_jk; eauto.
  Unshelve. all: eauto.
Qed.

Lemma b_res_chval_sc (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  sc_consistent (bounded_exec res (numbering k - 1)).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hres.
  inversion Hcomp as [Hval _]. inversion Hmcp as [Hscb _].
  eapply prefix_sc_consistent.
  - apply (smaller_than_smallest_sc _ bound Hval Hnumco Hrc11 Hscb (numbering k - 1)).
    eapply mcp_num_snd_evt_ord in Hmcp; auto. lia.
  - eapply b_res_chval_pre_b; eauto.
Qed.

Lemma dcmp_eco_chval (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  (sb res ⊔ rf res ⊔ mo res ⊔ rb res) ≦
  (((sb (bounded_exec res (numbering k - 1))) ⊔
    (rf (bounded_exec res (numbering k - 1))) ⊔
    (mo (bounded_exec res (numbering k - 1))) ⊔
    (rb (bounded_exec res (numbering k - 1)))) ⊔
   (((fun x y => x = c /\ y = Read (numbering k) (get_mode k) l v): rlt Event) ⊔
    (fun x y => ([I (sbrf_before_jk ex bound j k)]⋅sb ex⋅[I (sbrf_before_jk ex bound j k)]) x k /\
                y = Read (numbering k) (get_mode k) l v) ⊔
    (((fun x y => x = c /\ y = Read (numbering k) (get_mode k) l v): rlt Event)°⋅
     (mo (bounded_exec res (numbering k - 1)))))).
Proof.
  intros Hcomp Hnumco Hnuminj Hmcp Hord Hres.
  inversion Hcomp as [Hval _].
  inversion_res_chval Hres.
  intros x y [[[Hxy|Hxy]|Hxy]|Hxy].
  - rewrite Hsb in Hxy. destruct Hxy as [Hxy|Hxy].
    + apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
      destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hy) as [Hxk|Hxk].
      * left. left. left. left. rew bounded. 
        apply (sb_num_ord _ _ _ Hnumco) in Hxy as Hordxy. simpl_trt.
        -- unfold NLE. lia.
        -- rewrite Hsb. left. simpl_trt; auto.
        -- unfold NLE. lia.
      * right. left. right. rewrite Hxk in Hxy, Hy. split.
        -- simpl_trt; auto.
        -- eapply numbering_injective_eq; eauto. simpl. rewrite Hxk. auto.
    + right. left. right. auto.
  - rewrite Hrf in Hxy. destruct Hxy as [Hxy|Hxy].
    + apply simpl_trt_hyp in Hxy as [Hx [Hxy [Hy1 Hy2]]].
      destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hy1) as [Hxk|Hxk].
      * left. left. left. right. rew bounded.
        apply (rf_num_ord _ _ _ Hnumco) in Hxy as Hordxy. simpl_trt;
        try (unfold NLE; lia). rewrite Hrf. left. simpl_trt; auto.
        split; auto.
      * congruence.
    + right. left. left. auto.
  - left. left. right. rewrite Hmo in Hxy.
    apply simpl_trt_hyp in Hxy as [Hx [Hxy Hy]].
    destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hy) as [Hyk|Hyk];
    destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hx) as [Hxk|Hxk].
    + rew bounded. simpl_trt; try (unfold NLE; lia). rewrite Hmo.
      simpl_trt; auto.
    + apply (mo_orig_write _ Hval) in Hxy. rewrite Hxk in Hxy.
      destruct (not_wandr _ Hxy Hkr).
    + apply (mo_dest_write _ Hval) in Hxy. rewrite Hyk in Hxy.
      destruct (not_wandr _ Hxy Hkr).
    + apply (mo_dest_write _ Hval) in Hxy. rewrite Hyk in Hxy.
      destruct (not_wandr _ Hxy Hkr).
  - unfold rb in Hxy. destruct Hxy as [z Hxz Hzy]. rewrite <-cnv_rev in Hxz.
    rewrite Hrf in Hxz. rewrite Hmo in Hzy. destruct Hxz as [Hxz|Hxz].
    + apply simpl_trt_hyp in Hxz as [Hz1 [Hxz [Hx1 Hx2]]].
      apply simpl_trt_hyp in Hzy as [Hz2 [Hzy Hy]].
      destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hy) as [Hyk|Hyk];
      destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hx1) as [Hxk|Hxk].
      * apply (rf_num_ord _ _ _ Hnumco) in Hxz as Hzxord.
        left. right. exists z.
        -- rewrite <-cnv_rev. rew bounded. simpl_trt; try (unfold NLE; lia).
           rewrite Hrf. left. simpl_trt; auto. split; auto.
        -- rew bounded; simpl_trt; try (unfold NLE; lia). rewrite Hmo; simpl_trt; auto.
      * congruence.
      * rewrite Hyk in Hzy. apply (mo_dest_write _ Hval) in Hzy.
        destruct (not_wandr _ Hzy Hkr).
      * congruence.
    + destruct Hxz as [Hzc Hx]. apply simpl_trt_hyp in Hzy as [Hz [Hzy Hy]].
      destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hy) as [Hyk|Hyk];
      destruct (sbrf_before_jk_num _ _ _ _ _ Hnumco Hmcp Hord Hz) as [Hzk|Hzk].
      * right. right. exists z.
        -- rewrite <-cnv_rev. split; auto.
        -- rew bounded. simpl_trt; try (unfold NLE; lia). rewrite Hmo. simpl_trt. auto.
      * rewrite Hzk in Hzy. apply (mo_orig_write _ Hval) in Hzy. 
        destruct (not_wandr _ Hzy Hkr).
      * rewrite Hyk in Hzy. apply (mo_dest_write _ Hval) in Hzy.
        destruct (not_wandr _ Hzy Hkr).
      * apply (mo_diff _ Hval) in Hzy. congruence.
Qed.

(*
eapply (mo_irr _ Hval z5 z5); eauto. split; simpl; auto.
      eapply (mo_trans _ Hval _ z4).
      * rew bounded in Hend2. apply simpl_trt_rel in Hend2.
        rewrite Hmo in Hend2. apply simpl_trt_rel in Hend2. auto.
      * destruct Hmax as [_ [_ Hmax]].
        unshelve (epose proof (Hmax z4 _ _ _) as Hmax).
        -- apply (mo_dest_write _ Hbresval) in Hend2 as Hz4w.
           split; auto. rew bounded in Hend2. apply simpl_trt_rel in Hend2.
           rewrite Hmo in Hend2. apply simpl_trt_tright in Hend2. auto.
        -- apply (mo_same_loc _ Hbresval) in Hend2. rewrite Hend11, Hcloc in Hend2.
           congruence.
        -- intros Heq. rewrite Heq, Hend11 in Hend2. eapply (mo_irr _ Hbresval c c).
           split; auto. simpl. auto.
        -- apply simpl_trt_rel in Hmax.
           rewrite <-Hend11 in Hmax. auto.
*)

Lemma nothing_after_max_mo (ex res: Execution) (bound: nat) (j k c x: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  max_mo_for_loc c (sbrf_before_jk ex bound j k) (mo_res ex bound j k) l ->
  ~(mo (bounded_exec res (numbering k - 1)) c x).
Proof.
  intros Hcomp Hnumco Hnuminj Hmcp Hord Hres Hmax H.
  inversion_res_chval Hres.

  inversion Hcomp as [Hval _].
  assert (complete_exec (bounded_exec res (numbering k - 1))) as Hbrescomp.
  { eapply prefix_complete.
    - eapply complete_res_chval; eauto.
    - eapply bounded_exec_is_prefix; eauto.
      + eapply valid_res_chval; eauto.
      + eapply numco_res_chval; eauto.
  }
  inversion Hbrescomp as [Hbresval _].

  apply (mo_irr _ Hbresval c c). split; [|simpl; auto].
  eapply (mo_trans _ Hbresval _ x). auto.
  destruct Hmax as [_ [_ Hmax]].
  unshelve (epose proof (Hmax x _ _ _) as Hmax).
  - apply (mo_dest_write _ Hbresval) in H as Hxw.
    split; auto. rew bounded in H. apply simpl_trt_rel in H.
    rewrite Hmo in H. apply simpl_trt_tright in H. auto.
  - apply (mo_same_loc _ Hbresval) in H. rewrite <-H,Hcloc. auto.
  - apply (mo_diff _ Hbresval) in H. congruence.
  - apply bounded_mo_l in H as Hbc. apply bounded_mo_r in H as Hbx.
    rew bounded. simpl_trt; try (unfold NLE; lia).
    rewrite Hmo. apply Hmax.
Qed.

Lemma bounded_ecorb_l (res: Execution) (k x y: Event):
  (sb (bounded_exec res (numbering k - 1)) ⊔
   rf (bounded_exec res (numbering k - 1)) ⊔
   mo (bounded_exec res (numbering k - 1)) ⊔
   rb (bounded_exec res (numbering k - 1))) x y ->
  numbering x <= numbering k - 1.
Proof.
  intros [[[H|H]|H]|H].
  - apply bounded_sb_l in H. lia.
  - apply bounded_rf_l in H. lia.
  - apply bounded_mo_l in H. lia.
  - apply bounded_rb_l in H. lia.
Qed.

Lemma change_val_eco_ac1 (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  max_mo_for_loc c (sbrf_before_jk ex bound j k) (mo_res ex bound j k) l ->
  c <> j ->
  res_chval_k ex res bound j k c l v ->
  acyclic (sb res ⊔ rf res ⊔ mo res ⊔ rb res).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hmax Hdiff Hres.
  inversion Hcomp as [Hval _].
  inversion_res_chval Hres.
  intros x Hnot.
  apply (tc_incl _ _ (dcmp_eco_chval _ _ _ _ _ _ _ _ Hcomp Hnumco Hnuminj Hmcp Hord Hres)) in Hnot.

  assert (sc_consistent (bounded_exec res (numbering k - 1))) as [_ Hac].
  { eapply (b_res_chval_sc _ _ _ _ _ _ _ _ Hcomp); eauto. }

  apply (path_impl_pass_through _ _ _ _ (Hac x)) in Hnot.
  destruct Hnot as [z2 [z1 Hbeg Hmid] Hend].
  destruct Hmid as [Hmid _].
  rewrite rtc_inv_dcmp6 in Hbeg. rewrite rtc_inv_dcmp6 in Hend.
  rewrite tc_inv_dcmp2 in Hbeg. rewrite tc_inv_dcmp2 in Hend.
  destruct Hbeg as [Hbeg|[z3 Hbeg _]];
  destruct Hend as [Hend|[z4 Hend _]].
  - simpl in Hbeg. simpl in Hend.
    destruct Hmid as [[[Hmid1 Hmid2]|[Hmid1 Hmid2]]|[z3 [Hmid11 Hmid12] Hmid2]].
    + rewrite Hend, Hbeg, Hmid1 in Hmid2. rewrite Hmid2 in Hcw.
      unfold is_write in Hcw. auto.
    + apply (eq_num_read2 Hnuminj) in Hmid2.
      rewrite <-Hbeg, <-Hend, Hmid2 in Hmid1.
      apply simpl_trt_rel in Hmid1.
      eapply (sb_irr _ Hval); eauto. split; eauto. simpl. auto.
    + rew bounded in Hmid2. apply simpl_trt_rel in Hmid2.
      rewrite Hmo in Hmid2. apply simpl_trt_rel in Hmid2.
      rewrite Hend, Hbeg, Hmid12 in Hmid2.
      apply (mo_dest_write _ Hval) in Hmid2. intuition auto.
  - simpl in Hbeg.
    destruct Hmid as [[[Hmid1 Hmid2]|[Hmid1 Hmid2]]|[z3 [Hmid11 Hmid12] Hmid2]];
    [ | | rewrite Hmid11 in Hmid2; eapply (nothing_after_max_mo ex res); eauto];

    destruct Hend as [Hend|[[[Hend1 Hend2]|[Hend1 Hend2]]|[z5 [Hend11 Hend12] Hend2]]].
    + rewrite (eq_num_read2 Hnuminj Hmid2) in Hend. apply bounded_ecorb_l in Hend. lia.
    + rewrite <-Hend1, Hmid2 in Hcw. inversion Hcw.
    + apply (eq_num_read2 Hnuminj) in Hmid2. rewrite Hmid2 in Hend1.
      apply simpl_trt_rel in Hend1. eapply (sb_irr _ Hval); eauto. 
      split; eauto. simpl. auto.
    + rewrite Hend11 in Hend2.
      eapply (nothing_after_max_mo ex res); eauto.
    + rewrite (eq_num_read2 Hnuminj Hmid2) in Hend. apply bounded_ecorb_l in Hend. lia.
    + rewrite <-Hend1, Hmid2 in Hcw. inversion Hcw.
    + apply (eq_num_read2 Hnuminj) in Hmid2. rewrite Hmid2 in Hend1.
      apply simpl_trt_rel in Hend1. eapply (sb_irr _ Hval); eauto. split; eauto. simpl. auto.
    + rewrite Hend11 in Hend2. eapply (nothing_after_max_mo ex res); eauto.

  - simpl in Hend.
    destruct Hmid as [[[Hmid1 Hmid2]|[Hmid1 Hmid2]]|[z4 [Hmid11 Hmid12] Hmid2]];
    [ | | rewrite Hmid11 in Hmid2; eapply (nothing_after_max_mo ex res); eauto];

    destruct Hbeg as [Hbeg|[[[Hbeg1 Hbeg2]|[Hbeg1 Hbeg2]]|[z5 [Hbeg11 Hbeg12] Hbeg2]]].
    + rewrite <-Hend, (eq_num_read2 Hnuminj Hmid2) in Hbeg. apply bounded_ecorb_l in Hbeg. lia.
    + rewrite <-Hbeg1, <-Hend, Hmid2 in Hcw. intuition auto.
    + apply (eq_num_read2 Hnuminj) in Hmid2. rewrite <-Hend, Hmid2 in Hbeg1.
      apply simpl_trt_rel in Hbeg1. eapply (sb_irr _ Hval). split; eauto. simpl. auto.
    + rewrite Hbeg11 in Hbeg2.
      eapply (nothing_after_max_mo ex res); eauto.
    + rewrite <-Hend, (eq_num_read2 Hnuminj Hmid2) in Hbeg. apply bounded_ecorb_l in Hbeg. lia.
    + rewrite <-Hbeg1, <-Hend, Hmid2 in Hcw. intuition auto.
    + apply (eq_num_read2 Hnuminj) in Hmid2. rewrite <-Hend, Hmid2 in Hbeg1.
      apply simpl_trt_rel in Hbeg1. apply (sb_irr _ Hval k k). split; auto.
      simpl. auto.
    + rewrite Hbeg11 in Hbeg2. eapply (nothing_after_max_mo ex res); eauto.

  - destruct Hmid as [[[Hmid1 Hmid2]|[Hmid1 Hmid2]]|[z7 [Hmid11 Hmid12] Hmid2]];
    [ | | rewrite Hmid11 in Hmid2; eapply (nothing_after_max_mo ex res); eauto];

    destruct Hend as [Hend|[[[Hend1 Hend2]|[Hend1 Hend2]]|[z6 [Hend11 Hend12] Hend2]]];
    try (rewrite (eq_num_read2 Hnuminj Hmid2) in Hend; apply bounded_ecorb_l in Hend; lia);
    try (rewrite <-Hend1, Hmid2 in Hcw; intuition auto).

    destruct Hbeg as [Hbeg|[[[Hbeg1 Hbeg2]|[Hbeg1 Hbeg2]]|[z5 [Hbeg11 Hbeg12] Hbeg2]]];
    try (apply (eq_num_read2 Hnuminj) in Hmid2; rewrite Hmid2 in Hend1;
      apply simpl_trt_rel in Hend1; apply (sb_irr _ Hval k k); split; auto;
      simpl; auto).
    + rewrite Hend11 in Hend2. eapply (nothing_after_max_mo ex res); eauto.
    + apply (eq_num_read2 Hnuminj) in Hmid2; rewrite Hmid2 in Hend1;
      apply simpl_trt_rel in Hend1; apply (sb_irr _ Hval k k); split; auto;
      simpl; auto.
    + rewrite Hend11 in Hend2. eapply (nothing_after_max_mo ex res); eauto.
Qed.

Lemma change_val_eco_ac2 (ex res: Execution) (bound: nat) (j k c d: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  max_mo_for_loc c (sbrf_before_jk ex bound j k) (mo_res ex bound j k) l ->
  c = j ->
  (imm (mo ex)) d c ->
  res_chval_k ex res bound j k d l v ->
  acyclic (sb res ⊔ rf res ⊔ mo res ⊔ rb res).
Proof.

Admitted.

Lemma change_val_sc1 (ex res: Execution) (bound: nat) (j k c d: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  max_mo_for_loc c (sbrf_before_jk ex bound j k) (mo_res ex bound j k) l ->
  c <> j ->
  res_chval_k ex res bound j k c l v ->
  sc_consistent res.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hmaxmo Hdiff Hres.
  split.
  - eapply change_val_atomicity; eauto.
  - eapply change_val_eco_ac1; eauto.
Qed.

Lemma change_val_sc2 (ex res: Execution) (bound: nat) (j k c d: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  max_mo_for_loc c (sbrf_before_jk ex bound j k) (mo_res ex bound j k) l ->
  c = j ->
  (imm (mo ex)) d c ->
  res_chval_k ex res bound j k d l v ->
  sc_consistent res.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hmaxmo Hdiff Hres.
  split.
  - eapply change_val_atomicity; eauto.
  - eapply change_val_eco_ac2; eauto.
Qed.

(** the max mo is different from j *)

(** the max mo is j *)

(** The final proof *)
 
(** Two executions [a] is the same as the execution [b] modulo mo the only
difference is that [a] has a new, still valid, modification order *)

Definition eq_mod_mo (a b: Execution) :=
  (valid_mo (evts a) (mo a)) /\
  (evts a = evts b) /\
  (sb a = sb b) /\
  (rmw a = rmw b) /\
  (rf a = rf b).

Lemma eq_mod_mo_numco (a b: Execution):
  eq_mod_mo a b ->
  numbering_coherent b ->
  numbering_coherent a.
Proof.
  intros Heq Hnumco.
  intros x y Hsbrf.
  destruct Heq as [_ [_ [Hsb [_ Hrf]]]].
  rewrite Hsb, Hrf in Hsbrf. apply Hnumco. auto.
Qed.

Lemma eq_mod_mo_numinj (a b: Execution):
  eq_mod_mo a b ->
  numbering_injective b ->
  numbering_injective a.
Proof.
  intros Heq Hnuminj. split; intros H; apply Hnuminj; auto.
Qed.

(** An execution [a] stems from the same program than an execution [b] if:

- [a] is sb-closed restriction of [b]
- The only thing changing between [a] and [b] is the modification order
- We change the value write the last read of the execution (in the (sb ⊔ rf)^+
order) to another write in the execution.

The same-program relation is transitive *)

Inductive sameP (res ex: Execution) : Prop :=
  | sameP_pre : prefix res ex -> sameP res ex
  | sameP_res_chval : forall j k bound c v l,
      minimal_conflicting_pair ex bound j k ->
      numbering k > numbering j ->
      res_chval_k ex res bound j k c l v -> sameP res ex
  | sameP_mo : eq_mod_mo res ex -> sameP res ex
  | sameP_trans : forall c, sameP res c -> sameP c ex -> sameP res ex.

Lemma sameP_numbering_coherent (a b: Execution):
  sameP a b ->
  numbering_coherent b ->
  numbering_coherent a.
Proof.
  intros Hsame Hnumco.
  induction Hsame.
  - eapply numbering_coherent_pre; eauto.
  - eapply numco_res_chval; eauto.
  - eapply eq_mod_mo_numco; eauto.
  - intuition auto.
Qed.

Lemma sameP_numbering_injective (a b: Execution):
  sameP a b ->
  numbering_injective b ->
  numbering_injective a.
Proof.
  intros Hsame Hnumco.
  induction Hsame.
  - eapply numbering_injective_pre; eauto.
  - eapply numinj_res_chval; eauto.
  - eapply eq_mod_mo_numinj; eauto.
  - intuition auto.
Qed.

Lemma sameP_valid (a b: Execution):
  sameP a b ->
  valid_exec b ->
  numbering_coherent b ->
  numbering_injective b ->
  valid_exec a.
Proof.
  intros Hsame Hval Hnumco Hnuminj.
  induction Hsame as [a b Hpre| a b j k bound c v l Hmcp Hord Hchval|a b Hmo|a b c Ht1 IH1 Ht2 IH2].
  - eapply prefix_valid; eauto.
  - eapply valid_res_chval; eauto.
  - destruct Hmo as [Hvalmo [Hevts [Hsb [Hrmw Hrf]]]].
    unfold complete_exec, valid_exec in *.
    rewrite Hevts, Hsb, Hrmw, Hrf.
    rewrite Hevts in Hvalmo. intuition auto.
  - apply IH1.
    + apply IH2; auto.
    + eapply sameP_numbering_coherent; eauto.
    + eapply sameP_numbering_injective; eauto.
Qed.

Lemma sameP_complete (a b: Execution):
  sameP a b ->
  complete_exec b ->
  numbering_coherent b ->
  numbering_injective b ->
  complete_exec a.
Proof.
  intros Hsame Hval Hnumco Hnuminj.
  induction Hsame as [a b Hpre | a b j k bound c v l Hmcp Hord Hchval|a b Hmo|a b c Ht1 IH1 Ht2 IH2].
  - eapply prefix_complete; eauto.
  - eapply complete_res_chval; eauto.
  - destruct Hmo as [Hvalmo [Hevts [Hsb [Hrmw Hrf]]]].
    unfold complete_exec, valid_exec in *.
    rewrite Hevts, Hsb, Hrmw, Hrf.
    rewrite Hevts in Hvalmo. intuition auto.
  - apply IH1.
    + apply IH2; auto.
    + eapply sameP_numbering_coherent; eauto.
    + eapply sameP_numbering_injective; eauto.
Qed.

Lemma sameP_prefix_change_mo (ex: Execution) (bound: nat) (x y: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  is_write y ->
  numbering y > numbering x ->
  minimal_conflicting_pair ex bound x y ->
  (forall e', sameP e' ex ->
              sc_consistent e' ->
              (forall a b, (race e') a b ->
                          (get_mode a = Sc /\
                           get_mode b = Sc))) ->
  sameP (prefix_change_mo ex bound y) ex.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hw Hord Hmcp Hsc.
  apply (sameP_trans _ _ (bounded_exec ex bound)).
  - apply sameP_mo.
    unfold eq_mod_mo.
    split;[|split;[|split;[|split]]].
    + pose proof (mo_change_complete _ _ _ _ Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hw) as Hcomp'.
      destruct Hcomp' as [Hval' _].
      destruct Hval' as [_ [_ [_ [_ Hmo]]]].
      auto.
    + rew change_mo. auto.
    + rew change_mo. auto.
    + rew change_mo. auto.
      erewrite <-(write_rmw_eq_rmwbminone _ _ x y); eauto.
      eapply (mcp_write_not_sc _ _ y x); eauto.
      { eapply mcp_is_sym. auto. }
      intros pre Hpre Hsc'.
      eapply Hsc.
      * apply sameP_pre. auto.
      * auto.
    + rew change_mo. destruct Hcomp as [Hval _].
      pose proof (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord) as Hnum.
      rewrite <-(write_rf_eq_rfbminone _ _ _ Hval Hnumco Hnuminj Hnum Hw).
      auto.
  - apply sameP_pre. apply bounded_exec_is_prefix; auto.
    inversion Hcomp; auto.
Qed.

Lemma res_chval_not_sbrf_aux (ex: Execution) (bound: nat) (j k s: Event):
  valid_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  (rf ex) j s ->
  (sb ex) s k ->
  (get_mode j <> Sc \/ get_mode s <> Sc) ->
  pi (bounded_exec ex (numbering s)) j s.
Proof.
  intros Hval Hrc11 Hnumco Hmcp Hord Hjs Hsk (* Hsmod *) Hjmod.
  eapply (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp) in Hord as Hkbound.
  repeat (apply conj).
  - split.
    + eapply mcp_in_evts_left2. eauto.
    + unfold In. eapply (rf_num_ord _ _ _ Hnumco) in Hjs. lia.
  - split.
    + eapply rf_dest_evts; eauto.
    + unfold In. lia.
  - left. eapply rf_orig_write; eauto.
  - intros Heq. apply (rf_diff _ Hval) in Hjs. intuition auto.
  - eapply rf_same_loc; eauto.
  - intros [Hnot1 Hnot2]. intuition auto.
  - intros [Hnot|Hnot].
    + inversion Hmcp as [_ [_ H]].
      eapply (sb_num_ord _ _ _ Hnumco) in Hsk as Hordsk. 
      apply H. left. rewrite tc_inv_dcmp. exists s.
      * unshelve (eapply (sbrfsc_pre_inc (bounded_exec ex bound) _ 
                          (two_ord_bounds_pre _ (numbering s) _ _ _ _)) in Hnot);
        eauto; [|incl_rel_kat Hnot]. lia.
      * left. rew bounded. simpl_trt; unfold NLE; auto; lia.
    + rewrite <-cnv_rev in Hnot.
      apply sbrfsc_incl_sbrf in Hnot.
      apply (sbrf_pre_inc _ _ (bounded_exec_is_prefix _ _ Hval Hnumco)) in Hnot.
      destruct Hrc11 as [_ [_ [_ Hnothinair]]].
      apply (Hnothinair s). rewrite tc_inv_dcmp. exists j.
      * incl_rel_kat Hnot.
      * incl_rel_kat Hjs.
Qed.

Lemma res_chval_not_sbrf_j (ex res: Execution) (bound: nat) (j k c s: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  j <> c ->
  ~(sb res ⊔ rf res) j s.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hres Hdiffjc.
  inversion Hcomp as [Hval _].
  specialize (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord). intros Hkbound.
  inversion_res_chval Hres. rewrite Hsb, Hrf. intros [[Hnot|Hnot]|[Hnot|Hnot]].
  - apply simpl_trt_hyp in Hnot as [Hj [Hrel [Hsj|Hsk]]].
    + eapply (rtc_incl _ _ (sbrf_minone_sbrf _ _)) in Hsj.
      destruct Hrc11 as [_ [_ [_ Hnothinair]]].
      apply (Hnothinair j). rewrite tc_inv_dcmp2. exists s; auto.
      incl_rel_kat Hrel.
    + rewrite rtc_inv_dcmp6 in Hsk. destruct Hsk as [Hsk|Hsk].
      * simpl in Hsk. rewrite Hsk in Hrel. eapply mcp_not_sb_jk; eauto.
      * rewrite rtc_inv_dcmp8 in Hsk. destruct Hsk as [s' Hss' Hs'k].
        { destruct Hs'k as [Hs'k|Hs'k].
          - rewrite rtc_inv_dcmp6 in Hss'. destruct Hss' as [Hss'|Hss'].
            { simpl in Hss'. rewrite Hss' in Hrel.
              apply (mcp_not_sb_jk _ _ _ _ Hmcp).
              apply (sb_trans _ Hval j k). exists s'; auto. }
            eapply (tc_incl _ _ (sbrf_minone_sbrf _ _)) in Hss'.
            eapply sbbefore_lemma; eauto. eapply tc_inv_dcmp6.
            exists s.
            + incl_rel_kat Hrel.
            + incl_rel_kat Hss'.
          - rew bounded in Hs'k. apply simpl_trt_tright in Hs'k.
            unfold NLE in Hs'k. lia.
        }
  - destruct Hnot as [Hnot _].
    apply simpl_trt_rel in Hnot. eapply mcp_not_sb_jk; eauto.
  - apply simpl_trt_hyp in Hnot as [Hinj [Hrel [[Hsj|Hsk] Hdiff]]].
    + eapply (rtc_incl _ _ (sbrf_minone_sbrf _ _)) in Hsj.
      destruct Hrc11 as [_ [_ [_ Hnothinair]]].
      apply (Hnothinair j). rewrite tc_inv_dcmp2. exists s; auto.
      incl_rel_kat Hrel.
    + rewrite rtc_inv_dcmp6 in Hsk. destruct Hsk as [Hsk|Hsk].
      * simpl in Hsk. rewrite Hsk in Hrel. intuition auto.
      * rewrite rtc_inv_dcmp8 in Hsk. destruct Hsk as [s' Hss' Hs'k].
        { destruct Hs'k as [Hs'k|Hs'k].
          - rewrite rtc_inv_dcmp6 in Hss'. destruct Hss' as [Hss'|Hss'].
            + { simpl in Hss'. rewrite Hss' in Hrel.
                apply (sb_num_ord _ _ _ Hnumco) in Hs'k as Hords'k.
                destruct (classic (get_mode s' = Sc)) as [Hs'|Hs'].
                - destruct (classic (get_mode j = Sc)) as [Hj|Hj].
                  + destruct Hmcp as [_ [_ Hnot]].
                    apply Hnot. left. apply tc_inv_dcmp8.
                    exists s'; apply tc_incl_itself.
                    * right. apply res_mode_conds. split;[|split]; auto.
                      rew bounded. simpl_trt; unfold NLE; auto; lia.
                    * left. rew bounded. simpl_trt; unfold NLE; auto; lia.
                  + inversion Hmcp as [[_ Hsmallest] _].
                    unshelve (epose proof (Hsmallest (numbering s') _)); [|try lia].
                    exists j, s'.
                    eapply (res_chval_not_sbrf_aux _ _ j k s'); eauto.
                - inversion Hmcp as [[_ Hsmallest] _].
                  unshelve (epose proof (Hsmallest (numbering s') _)); [|try lia].
                  exists j, s'.
                  eapply (res_chval_not_sbrf_aux _ _ j k s'); eauto.
              }
            + eapply (sbbefore_lemma _ _ _ _ s'); eauto.
              rewrite tc_inv_dcmp2. exists s.
              * incl_rel_kat Hrel.
              * rew bounded in Hss'. incl_rel_kat Hss'.
          - rew bounded in Hs'k. apply simpl_trt_tright in Hs'k.
            specialize (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord).
            intros Hnum. unfold NLE in Hs'k. lia.
        }
  - destruct Hnot as [Hjc Hs]. intuition auto.
Qed.

Lemma res_chval_not_sbrf_k (ex res: Execution) (bound: nat) (j k c s: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  j <> c ->
  ~(sb res ⊔ rf res) k s.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hres Hdiff Hnot.
  inversion Hcomp as [Hval _].
  inversion_res_chval Hres.
  destruct Hnot as [Hnot|Hnot].
  - rewrite Hsb in Hnot. destruct Hnot as [Hnot|[Hnot _]].
    + apply simpl_trt_rel in Hnot as Hks.
      apply simpl_trt_tright in Hnot.
      specialize (sbrf_before_jk_bounded _ _ _ _ _ Hval Hnumco Hmcp Hord Hnot).
      intros H. rewrite simpl_evts_be in H. apply in_intersection in H as [_ H].
      unfold In in H. apply (sb_num_ord _ _ _ Hnumco) in Hks.
      specialize (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord). intros Hnum.
      lia.
    + apply simpl_trt_rel in Hnot. eapply sb_irr; eauto. split; eauto. simpl. auto.
  - apply rf_orig_write in Hnot.
    + destruct k; unfold is_read in Hkr; unfold is_write in Hnot; intuition auto.
    + eapply sameP_valid; eauto.
      eapply sameP_res_chval; eauto.
Qed.

Lemma res_chval_race (ex res: Execution) (bound: nat) (j k c: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c l v ->
  j <> c ->
  (race res) j k /\ (get_mode j <> Sc \/ get_mode k <> Sc).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hres Hdiff.
  inversion Hcomp as [Hval _].
  repeat (apply conj).
  - eapply mcp_one_is_write; eauto.
  - eapply mcp_diff; eauto.
  - eapply mcp_same_loc; eauto.
  - intros Hhb. unfold hb in Hhb.
    rewrite tc_inv_dcmp2 in Hhb. destruct Hhb as [s [Hhb|Hhb] _].
    + eapply res_chval_not_sbrf_j; eauto.
      incl_rel_kat Hhb.
    + eapply sw_incl_sbrf in Hhb.
      { rewrite tc_inv_dcmp2 in Hhb. destruct Hhb as [s' [Hhb|Hhb] _].
        * eapply res_chval_not_sbrf_j; eauto. incl_rel_kat Hhb.
        * eapply res_chval_not_sbrf_j; eauto. incl_rel_kat Hhb. }
      eapply sameP_valid; eauto.
      eapply sameP_res_chval; eauto.
  - intros Hhb. unfold hb in Hhb.
    rewrite tc_inv_dcmp2 in Hhb. destruct Hhb as [s [Hhb|Hhb] _].
    + eapply res_chval_not_sbrf_k; eauto.
      incl_rel_kat Hhb.
    + eapply sw_incl_sbrf in Hhb.
      { rewrite tc_inv_dcmp2 in Hhb. destruct Hhb as [s' [Hhb|Hhb] _].
        * eapply res_chval_not_sbrf_k; eauto. incl_rel_kat Hhb.
        * eapply res_chval_not_sbrf_k; eauto. incl_rel_kat Hhb. }
      eapply sameP_valid; eauto.
      eapply sameP_res_chval; eauto.
  - unshelve (epose proof (mcp_not_sc ex bound j k _) as H); eauto.
    apply not_and_or in H. intuition auto.
Qed.

Lemma drf_sc (e: Execution):
  complete_exec e ->
  numbering_coherent e ->
  numbering_injective e ->
  (forall e', sameP e' e ->
              sc_consistent e' ->
              (forall a b, (race e') a b ->
                          (get_mode a = Sc /\
                           get_mode b = Sc))) ->
  (exists e', sameP e' e /\
              rc11_consistent e' /\
              ~(sc_consistent e')) ->
  (exists e', sameP e' e /\
              sc_consistent e' /\
              (exists a b, (race e') a b /\
                           (get_mode a <> Sc \/
                            get_mode b <> Sc))).
Proof.
  intros Hcomp Hnumco Hnuminj Hsc [e' [Hsame [Hrc11 Hnotsc]]].
  inversion Hcomp as [Hval _].

  (* An execution that is not SC contains a conflict *)
  pose proof (exec_sc_no_conflict e' (sameP_valid _ _ Hsame (proj1 Hcomp) Hnumco Hnuminj) Hrc11 Hnotsc) as Hexpi.
  (* An execution that contains a conflict must have a minimal conflicting 
    pair *)
  destruct (mcp_exists_ord _ Hexpi Hnuminj) as [b [j [k [Hmcp Hord]]]].

  (* The smallest conflicting bounding is complete *)
  assert (complete_exec (bounded_exec e' b)) as Hscbcomp.
  { eapply sameP_complete; eauto.
    eapply sameP_trans with e'; eauto.
    eapply sameP_pre, bounded_exec_is_prefix.

    - eapply sameP_valid; eauto.
    - eapply sameP_numbering_coherent; eauto. }

  (* e' is complete *)
  assert (complete_exec e') as He'comp.
  { eapply sameP_complete; eauto. }
  inversion He'comp as [He'val _].

  (* The numbering of e' is coherent *)
  assert (numbering_coherent e') as He'numco.
  { eapply sameP_numbering_coherent; eauto. }

  (* The first event introducing a conflict in the execution is either a read or
     a write *)
  destruct (mcp_readwrite_r _ _ _ _ Hmcp) as [Hkw|Hkr].

  (* If this event is a write *)
  - (* The smallest conflicting bounding is not sc *)
    assert (~(sc_consistent (bounded_exec e' b))) as Hscbnotsc.
    { eapply (mcp_write_not_sc _ _ k j); eauto.
      - eapply mcp_is_sym; eauto.
      - intros pre Hpre Hsc'. eapply Hsc; eauto.
        eapply sameP_trans with e'; eauto.
        eapply sameP_pre. auto.
    }
    exists (prefix_change_mo e' b k).
    split;[|split].
    + apply (sameP_trans _ _ e'); auto.
      apply (sameP_prefix_change_mo _ _ j k); eauto.
      intros x y z. eapply Hsc; eauto.
      eapply sameP_trans; eauto.
    + eapply sc_racy_exec; eauto.
    + exists j, k. split.
      * apply race_implies_race_change_mo; eauto.
        eapply race_sym. eapply mcp_write_race; eauto.
        eapply mcp_is_sym; eauto.
      * eapply mcp_at_least_one_not_sc in Hmcp.
        destruct (classic (get_mode j <> Sc));
        destruct (classic (get_mode k <> Sc));
        intuition auto.

  (* If this event is a read *)

  - assert (is_write j) as Hwj.
    { destruct (mcp_one_is_write _ _ _ _ Hmcp) as [Hk|Hk]. 
        + auto.
        + destruct k; unfold is_write, is_read in Hk, Hkr;
          intuition auto. }

    destruct (loc_of_write _ Hwj) as [l Hloc].
    edestruct (exists_max_mo_for_loc
                (sbrf_before_jk e' b j k)
                (mo_res e' b j k) 
                l) as [c Hmax].
    { admit. }

    destruct (classic (c = j)) as [Hjc|Hjc].
    + destruct (max_mo_has_predecessor _ _ _ _ _ _ Hmcp Hmax Hjc) as [d [Hdloc Himmdc]].
      inversion Himmdc as [Hdw _]. apply (mo_orig_write _ He'val) in Hdw.
      destruct (val_of_write _ Hdw) as [v Hdval].
      destruct (res_chval_exists e' b j k d l v) as [res Hres]; auto.
      { admit. }
      exists res. split;[|split].
      * eapply sameP_trans.
        eapply sameP_res_chval; eauto. eauto.
      * eapply change_val_sc2; eauto.
      * exists j, k. eapply res_chval_race; eauto.
        destruct Himmdc as [Hdc _]. apply (mo_diff _ He'val) in Hdc. congruence.
    + inversion Hmax as [[_ Hcw] _].
      inversion Hmax as [_ [Hcloc _]].
      destruct (val_of_write _ Hcw) as [v Hcval].
      destruct (res_chval_exists e' b j k c l v) as [res Hres]; auto.
      { destruct Hmax as [[? _] _]. auto. }
      exists res. split;[|split].
      * eapply sameP_trans.
        eapply sameP_res_chval; eauto. eauto.
      * eapply change_val_sc1; eauto.
      * exists j, k. eapply res_chval_race; eauto.
Admitted.

Lemma drf_sc_final (e: Execution):
  complete_exec e ->
  numbering_coherent e ->
  numbering_injective e ->
  (* If all the SC executions of a program are race-free *)
  (forall e', sameP e' e ->
              sc_consistent e' ->
              (forall a b, (race e') a b ->
                          (get_mode a = Sc /\
                           get_mode b = Sc))) ->
  (* All the RC11-consistent executions of the program are SC-consistent *)
  (forall e', sameP e' e ->
              rc11_consistent e' ->
              sc_consistent e').
Proof.
  intros Hcomp Hnumco Hnuminj H e' Hsame Hrc11.
  byabsurd. exfalso.
  pose proof (drf_sc e Hcomp) as Hstep.
  destruct Hstep as [e'' [Hsame' [Hsc' [a [b [Hrace Hmode]]]]]]; auto.
  { exists e'. split;[|split]; auto. }
  specialize (H e'' Hsame' Hsc' a b Hrace).
  intuition auto.
Qed.

End DRF.












