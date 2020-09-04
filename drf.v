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

(** ** The first conflicting event is a read *)



(* I approched the sb-closed restriction and the addition of a new rf edge in 
the second part of the proof seperatly, but it does not make sense. Keeping this
for reference *)

(*
Definition sb_closed_restriction (ex res: Execution) (e: Ensemble Event) :=
  Included _ e (evts ex) /\
  (forall a b, In _ e b -> (sb ex) a b -> In _ e a) /\
  evts res = e /\
  sb res = [I e]⋅sb ex⋅[I e] /\
  rf res = [I e]⋅rf ex⋅[I e] /\
  mo res = [I e]⋅mo ex⋅[I e] /\
  rmw res = [I e]⋅rmw ex⋅[I e].

Ltac destruct_res H :=
  let H1 := fresh "Hinc" in
  let H2 := fresh "Hclo" in
  let H3 := fresh "Hevts" in
  let H4 := fresh "Hsb" in
  let H5 := fresh "Hrf" in
  let H6 := fresh "Hmo" in
  let H7 := fresh "Hrmw" in
  destruct H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].

Ltac inversion_res H :=
  let H1 := fresh "Hinc" in
  let H2 := fresh "Hclo" in
  let H3 := fresh "Hevts" in
  let H4 := fresh "Hsb" in
  let H5 := fresh "Hrf" in
  let H6 := fresh "Hmo" in
  let H7 := fresh "Hrmw" in
  inversion H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].

Lemma numbering_coherent_sbres (ex res: Execution) (e: Ensemble Event):
  numbering_coherent ex ->
  sb_closed_restriction ex res e ->
  numbering_coherent res.
Proof.
  intros Hnumco Hres. destruct_res Hres.
  intros x y [Hxy|Hxy]; [rewrite Hsb in Hxy|rewrite Hrf in Hxy];
  apply simpl_trt_rel in Hxy; apply Hnumco; [left|right]; auto.
Qed.

Lemma numbering_injective_sbres (ex res: Execution) (e: Ensemble Event):
  numbering_injective ex ->
  sb_closed_restriction ex res e ->
  numbering_injective res.
Proof.
  intros Hnuminj Hres. split; intros H; apply Hnuminj; auto.
Qed.

Lemma num_in_sbrf_before_jk (ex: Execution) (bound: nat) (j k x: Event):
  numbering_coherent ex ->
  numbering k > numbering j ->
  In _ (sbrf_before_jk ex bound j k) x ->
  numbering k >= numbering x.
Proof.
  intros Hnumco Hord [Hx|Hx].
  - assert ((sb ex ⊔ rf ex)^* x j).
    { apply (incl_rel_thm Hx). rew bounded. kat. }
    apply numbering_coherent_rtc in H. lia. auto.
  - assert ((sb ex ⊔ rf ex)^* x k).
    { apply (incl_rel_thm Hx). rew bounded. kat. }
    apply numbering_coherent_rtc in H. lia. auto.
Qed.

Lemma sb_closed_res_v_evts (ex res: Execution) (e: Ensemble Event):
  valid_evts (evts ex) ->
  sb_closed_restriction ex res e ->
  valid_evts (evts res).
Proof.
  intros [Hval1 Hval2] Hres. destruct_res Hres.
  split.
  - intros e1 e2 He1 He2.
    rewrite Hevts in He1, He2.
    apply Hinc in He1. apply Hinc in He2.
    apply (Hval1 e1 e2 He1 He2).
  - intros e1 He1. rewrite Hevts in He1.
    apply Hinc in He1. apply (Hval2 e1 He1).
Qed.

Lemma sb_closed_res_lso (ex res: Execution) (e: Ensemble Event):
  linear_strict_order (sb ex) (evts ex) ->
  sb_closed_restriction ex res e ->
  linear_strict_order (sb res) (evts res).
Proof.
  intros [[Hincl [Htrans Hirr]] Htot] Hres. destruct_res Hres.
  split;[split;[|split]|].
  - rewrite Hevts, Hsb. kat_eq.
  - rewrite Hsb. rewrite <-Htrans at 3. kat.
  - intros x Hnot. apply (Hirr x). rewrite Hsb in Hnot.
    apply simpl_trt_rel in Hnot. auto.
  - intros x y Hdiff Hx Hy.
    rewrite Hsb.
    rewrite Hevts in Hx. rewrite Hevts in Hy.
    assert (Hxe := Hx). assert (Hye := Hy).
    apply Hinc in Hx. apply Hinc in Hy.
    destruct (Htot x y Hdiff Hx Hy) as [Hfin|Hfin];
    [left|right]; simpl_trt; auto.
Qed.
  
Lemma sb_closed_res_v_sb (ex res: Execution) (es: Ensemble Event):
  valid_sb (evts ex) (sb ex) ->
  sb_closed_restriction ex res es ->
  valid_sb (evts res) (sb res).
Proof.
  intros [Hlso Hval] Hres.
  inversion_res Hres.
  split.
  { eauto using sb_closed_res_lso. }
  intros l. destruct (Hval l) as [e [Hloc [Hvalue [Hnote Hran]]]].
  exists e. splitall; auto.
  - intros Hnot. apply Hnote.
    eapply (elt_ran_incl _ _ _ _ Hnot).
    Unshelve. rewrite Hsb. kat.
  - intros e' Hinsbpre. rewrite Hsb.
    rewrite Hsb in Hinsbpre.
    simpl_trt;
    eapply ran_trt in Hinsbpre as [Hine' [y [Hine Hr]]].
    + eapply (Hclo _ e'); eauto.
      eapply Hran. exists y. eauto.
    + eapply Hran. exists y. eauto.
    + auto.
Qed.

Lemma sb_closed_res_imm_sb (ex res: Execution) (es: Ensemble Event) (r w: Event):
  imm (sb ex) r w ->
  sb_closed_restriction ex res es ->
  rmw res r w ->
  imm (sb res) r w.
Proof.
  intros Himm Hpre Hrmwpre.
  inversion_res Hpre.
  unfold imm in Himm.
  destruct Himm as [Hsbimm H]. split.
  - rewrite Hrmw in Hrmwpre. rewrite Hsb.
    apply simpl_trt_hyp in Hrmwpre as [? [? ?]]; 
    simpl_trt; auto.
  - intros c Hsbpre. rewrite Hsb in Hsbpre. rewrite Hrmw in Hrmwpre.
    apply simpl_trt_hyp in Hsbpre as [? [Hsbex ?]].
    apply simpl_trt_hyp in Hrmwpre as [? [Hrmwpre ?]].
    destruct (H c Hsbex) as [Href H']. split.
    + destruct Href.
      * left. rewrite Hsb. simpl_trt; auto.
      * right. auto.
    + intros c' Hsbpre. rewrite Hsb in Hsbpre.
      apply simpl_trt_hyp in Hsbpre as [? [Hsbrc ?]].
      pose proof (H' c' Hsbrc) as [Hsbwc' | Href'].
      * left. rewrite Hsb. simpl_trt. auto.
      * right. auto.
Qed.

Lemma sb_closed_res_rmw_pair_valid (ex res: Execution) (es: Ensemble Event) (r w: Event):
  valid_rmw_pair (sb ex) r w ->
  sb_closed_restriction ex res es ->
  rmw res r w ->
  valid_rmw_pair (sb res) r w.
Proof.
  intros Hvalpair Hpre Hrmw.
  unfold valid_rmw_pair in *.
  destruct (get_mode r); destruct (get_mode w); auto;
  destruct Hvalpair as [Hisr [Hisw [Hgetl Himm]]];
  (split;[|split;[|split]]);
  eauto using sb_closed_res_imm_sb.
Qed.


Lemma sb_closed_res_v_rmw (ex res: Execution) (es: Ensemble Event):
  valid_rmw (evts ex) (sb ex) (rmw ex) ->
  sb_closed_restriction ex res es ->
  valid_rmw (evts res) (sb res) (rmw res).
Proof.
  intros Hval Hres.
  inversion_res Hres.
  destruct_rmw_v Hval.
  split.
  - intros r w Hrmwpre.
    eapply sb_closed_res_rmw_pair_valid; eauto.
    apply Hrmw_vpairs.
    rewrite Hrmw in Hrmwpre. incl_rel_kat Hrmwpre.
  - rewrite Hrmw, Hevts. kat_eq.
Qed.

Lemma sb_closed_res_v_rf (ex res: Execution) (es: Ensemble Event):
  valid_rf (evts ex) (rf ex) ->
  sb_closed_restriction ex res es ->
  valid_rf (evts res) (rf res).
Proof.
  intros Hrf_v Hres.
  inversion_res Hres. destruct_rf_v Hrf_v.
  repeat (apply conj).
  - intros w r Hrfres.
    eapply Hrfco. rewrite Hrf in Hrfres.
    incl_rel_kat Hrfres.
  - rewrite Hrf, Hevts. kat_eq.
  - rewrite Hrf. rewrite <-Hrfwr. kat_eq.
  - intros w1 w2 r [Hrfpre1 Hrfpre2].
    eapply Hrfun. split.
    + rewrite Hrf in Hrfpre1. incl_rel_kat Hrfpre1.
    + rewrite Hrf in Hrfpre2. incl_rel_kat Hrfpre2.
Qed.

Lemma sb_closed_res_v_mo (ex res: Execution) (es: Ensemble Event):
  valid_mo (evts ex) (mo ex) ->
  sb_closed_restriction ex res es ->
  valid_mo (evts res) (mo res).
Proof.
  intros Hmo_v Hres.
  inversion_res Hres. destruct_mo_v Hmo_v.
  split;[|split; [|split]].
  - rewrite Hmo, <- Hmoww. kat_eq.
  - intros x y Hmopre. rewrite Hmo in Hmopre.
    apply simpl_trt_hyp in Hmopre. eapply Hmosameloc.
    intuition eauto.
  - split;[|split]; destruct Hmopo as [_ [Hmotrans Hmoirr]].
    + rewrite Hmo, Hevts. kat_eq.
    + rewrite Hmo. rewrite <- Hmotrans at 3. kat.
    + eapply incl_irr. eauto. rewrite Hmo. kat.
  - intros l x y Hdiff Hin1 Hin2.
    inversion Hin1 as [Hine1 _]. inversion Hin2 as [Hine2 _].
    assert (Included _ (evts res) (evts ex)) as Hincl.
    { intros z H. rewrite Hevts in H. apply Hinc in H. auto. }
    apply (writes_loc_incl _ _ _ _ Hincl) in Hin1.
    apply (writes_loc_incl _ _ _ _ Hincl) in Hin2.
    destruct (Hmotot l x y Hdiff Hin1 Hin2) as [[? [? ?]]|[? [? ?]]]; [left|right];
    split.
    + rewrite Hmo. simpl_trt. 
      * rewrite Hevts in Hine1. auto.
      * auto.
      * rewrite Hevts in Hine2. auto.
    + intuition auto.
    + rewrite Hmo. simpl_trt. 
      * rewrite Hevts in Hine2. auto.
      * auto.
      * rewrite Hevts in Hine1. auto.
    + intuition auto.
Qed.

Lemma sb_closed_res_valid (ex res: Execution) (e: Ensemble Event):
  valid_exec ex ->
  sb_closed_restriction ex res e ->
  valid_exec res.
Proof.
  intros Hval Hres.
  destruct_val_exec Hval.
  split;[|split;[|split;[|split]]].
  - eapply sb_closed_res_v_evts; eauto.
  - eapply sb_closed_res_v_sb; eauto.
  - eapply sb_closed_res_v_rmw; eauto.
  - eapply sb_closed_res_v_rf; eauto.
  - eapply sb_closed_res_v_mo; eauto.
Qed.

Lemma sb_closed_res_complete (ex res: Execution) (e: Ensemble Event):
  complete_exec ex -> 
  sb_closed_restriction ex res e ->
  complete_exec res.
Proof.
  intros [Hval Hcomp] Hres.
  split.
  - eapply sb_closed_res_valid; eauto.
  - (* A sb_closed_restriction of an execution is still valid, but it is not
       necessary complete. In the following execution:

       a --> b --> c --> d

       e --> f --> g --> h

      where c reads-from h, we might restrict it to the sb-closed subset of 
      events {a, b, c, e, f, g}, and c will read its value from nowhere in this
      execution
     *)
Abort.
    

Lemma prefix_implies_res (ex pre: Execution):
  prefix pre ex ->
  exists e, sb_closed_restriction ex pre e.
Proof.
  intros Hpre.
  destruct_prefix Hpre.
  exists (evts pre).
  repeat (apply conj); auto.
  intros a b Hinb Hab.
  eapply Hclosed.
  - left. eauto.
  - eauto.
Qed.

Lemma sb_res_exists (ex: Execution) (bound: nat) (j k: Event):
  valid_exec ex ->
  minimal_conflicting_pair ex bound j k ->
  exists res, sb_closed_restriction ex res (sbrf_before_jk ex bound j k).
Proof.
  intros Hval Hmcp.
  pose (sbrf_before_jk ex bound j k) as e.
  exists (mkex e
               ([I e]⋅sb ex⋅[I e])
               ([I e]⋅rmw ex⋅[I e])
               ([I e]⋅rf ex⋅[I e])
               ([I e]⋅mo ex⋅[I e])).
  unfold sb_closed_restriction.
  repeat (apply conj); auto.
  - intros x [H|H].
    + eapply rtc_sbrf_in_l.
      * auto.
      * eapply mcp_in_evts_left2. eauto.
      * apply (incl_rel_thm H). rew bounded. kat.
    + eapply rtc_sbrf_in_l.
      * auto.
      * eapply mcp_in_evts_right2. eauto.
      * apply (incl_rel_thm H). rew bounded. kat.
  - intros a b [Hb|Hb] Hsb;[left|right].
    + apply rtc_inv_dcmp2. exists b.
      * incl_rel_kat Hsb.
      * auto.
    + apply rtc_inv_dcmp2. exists b.
      * incl_rel_kat Hsb.
      * auto.
Qed.

(*
Lemma prefix_res_ex (ex res: Execution) (bound: nat) (j k: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  sb_closed_restriction ex res (sbrf_before_jk ex bound j k) ->
  prefix res ex.
Proof.
  intros Hcomp Hrc11 Hnumco Hmcp Hord Hres.
  inversion_res Hres.
  repeat (apply conj).
  - rewrite Hevts. auto.
  - intros a b Hsbrf Hb.
    rewrite Hevts in *.
    unfold In in *. unfold sbrf_before_jk.
    destruct Hb as [Hb|Hb].
    + left. apply rtc_inv_dcmp2. exists b; auto.
      destruct Hsbrf; [left|right]; auto.
      assert ((sb ex ⊔ rf (bounded_exec ex bound))^* ≦ (sb ex ⊔ rf ex)^* ) as Hgen.
      { rew bounded. kat. }
      apply Hgen in Hb. apply (numbering_coherent_rtc _ _ _ Hnumco) in Hb.
      rew bounded. apply mcp_left_le_bound in Hmcp as Hj.
      apply mcp_right_le_bound in Hmcp as Hk.
      apply (rf_num_ord _ _ _ Hnumco) in H as Hrford. solve_trt_bounds.
    + right. apply rtc_inv_dcmp2. exists b; auto.
      destruct Hsbrf; [left|right]; auto.
      assert ((sb ex ⊔ rf (bounded_exec ex bound))^* ≦ (sb ex ⊔ rf ex)^* ) as Hgen.
      { rew bounded. kat. }
      apply Hgen in Hb. apply (numbering_coherent_rtc _ _ _ Hnumco) in Hb.
      rew bounded. apply mcp_right_le_bound in Hmcp.
      apply (rf_num_ord _ _ _ Hnumco) in H as Hrford. solve_trt_bounds.
  - rewrite Hsb, Hevts. auto.
  - rewrite Hrf, Hevts. auto.
  - rewrite Hmo, Hevts. auto.
  - rewrite Hrmw, Hevts. auto.
Qed.
*)

Lemma pi_in_res (ex res: Execution) (bound: nat) (j k: Event):
  pi (bounded_exec ex bound) j k ->
  sb_closed_restriction ex res (sbrf_before_jk ex bound j k) ->
  prefix res ex ->
  pi (bounded_exec res bound) j k.
Proof.
  intros Hpi Hres Hpre.
  inversion_res Hres.
  destruct Hpi as [[Hconf Hsc] Hnotsbrf]. 
  split;[split|]; auto.
  - destruct Hconf as [H1 [H2 [H3 [H4 H5]]]].
    repeat (apply conj); auto.
    + rewrite simpl_evts_be. rewrite simpl_evts_be in H1. 
      apply in_intersection in H1 as [H11 H12].
      split.
      * rewrite Hevts. unfold sbrf_before_jk. left.
        apply one_incl_rtc. simpl; auto.
      * cbv. eauto.
    + rewrite simpl_evts_be. rewrite simpl_evts_be in H2.
      apply in_intersection in H2 as [H21 H22].
      split.
      * rewrite Hevts. unfold sbrf_before_jk. right.
        apply one_incl_rtc. simpl; auto.
      * cbv. eauto.
  - assert ((sb (bounded_exec res bound) ⊔
             res_mode Sc (rf (bounded_exec res bound)))^+ ≦
            (sb (bounded_exec ex bound) ⊔
             res_mode Sc (rf (bounded_exec ex bound)))^+).
    { apply sbrfsc_pre_inc.
      apply bounding_of_prefix. auto. }
    intros [Hnot|Hnot]; apply Hnotsbrf; [left|right].
    + apply (incl_rel_thm Hnot). auto.
    + rewrite <-cnv_rev in Hnot. rewrite <-cnv_rev.
      apply (incl_rel_thm Hnot). auto.
Qed.

Lemma expi_in_res (ex res: Execution) (bound: nat) (j k: Event):
  pi (bounded_exec ex bound) j k ->
  sb_closed_restriction ex res (sbrf_before_jk ex bound j k) ->
  prefix res ex ->
  expi (bounded_exec res bound).
Proof.
  intros Hpi Hres Hpre.
  exists j, k.
  apply (pi_in_res _ _ _ _ _ Hpi Hres Hpre).
Qed.

(*
Lemma mcp_in_res (ex res: Execution) (bound: nat) (j k: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  sb_closed_restriction ex res (sbrf_before_jk ex bound j k) ->
  minimal_conflicting_pair res bound j k.
Proof.
  intros Hcomp Hrc11 Hnumco Hmcp Hord Hres.
  inversion Hmcp as [[Hexpi Hsmallest] Hpi].
  split;[split|].
  - eapply expi_in_res; eauto. eapply prefix_res_ex; eauto.
  - intros n Hexpi2. eapply Hsmallest.
    unshelve (eapply (expi_prefix _ _ _ Hexpi2)).
    apply bounding_of_prefix. eapply prefix_res_ex; eauto.
  - eapply pi_in_res; eauto. eapply prefix_res_ex; eauto.
Qed.
*)

(*
Lemma res_reads_ranrf (ex res: Execution) (bound: nat) (j k: Event):
  complete_exec ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  sb_closed_restriction ex res (sbrf_before_jk ex bound j k) ->
  Included _ (reads (evts res)) (ran (rf res)).
Proof.
  intros Hcomp Hnumco Hmcp Hord Hres. inversion Hcomp as [Hval _]. destruct_res Hres.
  rewrite Hevts, Hrf. intros x [H Hxr].
  assert (In _ (ran (rf ex)) x) as [y Hrel].
  { destruct Hcomp as [_ Hcomp].
    apply Hcomp. apply conj; auto. }
  assert (numbering y < numbering x) as Hord2.
  { eapply Hnumco. right. auto. }
  destruct H as [H|H].
  - exists y, x.
    + exists y; auto. split; auto.
      left.
      assert ((sb ex ⊔ rf ex)^* x j) as Hxj.
      { rew bounded in H; incl_rel_kat H. }
      eapply (numbering_coherent_rtc _ _ _ Hnumco) in Hxj.
      rewrite (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord) in Hord.
      eapply rtc_inv_dcmp2. exists x; auto.
      rew bounded. right. solve_trt_bounds.
    + split; auto. left; auto.
  - 
  exists y, x.
  - assert (numbering y < numbering x) as Hord2.
    { eapply Hnumco. right. auto. }
    exists y; auto. split; auto.
    destruct H as [H|H]; [left|right].
    + assert ((sb ex ⊔ rf ex)^* x j) as Hxj.
      { rew bounded in H; incl_rel_kat H. }
      eapply (numbering_coherent_rtc _ _ _ Hnumco) in Hxj.
      rewrite (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord) in Hord.
      eapply rtc_inv_dcmp2. exists x; auto.
      rew bounded. right. solve_trt_bounds.
    + exists x.
      * rew bounded. right.

  
Lemma res_complete (ex res: Execution) (bound: nat) (j k: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  sb_closed_restriction ex res (sbrf_before_jk ex bound j k) ->
  complete_exec res.
Proof.
  intros Hcomp Hrc11 Hnumco Hmcp Hord Hres.
  split.
  - eapply sb_closed_res_valid; destruct Hcomp; eauto.
  - intros 
Qed.

*)

Lemma res_of_bound (ex res: Execution) (bound: nat) (e: Ensemble Event):
  numbering_coherent ex ->
  sb_closed_restriction (bounded_exec ex bound) res e ->
  sb_closed_restriction ex res e.
Proof.
  intros Hnumco Hres.
  inversion_res Hres.
  repeat (apply conj).
  - rewrite simpl_evts_be in Hinc. intros x H.
    apply Hinc in H. apply in_intersection in H as [H _]. auto.
  - intros a b Hin Hab. eapply Hclo.
    + eauto.
    + apply (sb_num_ord _ _ _ Hnumco) in Hab as Habord.
      apply Hinc in Hin as Hin2.
      rewrite simpl_evts_be in Hin2. apply in_intersection in Hin2 as [_ Hin2].
      unfold In in Hin2. rew bounded. solve_trt_bounds.
  - auto.
  - rewrite Hsb. rew bounded.
    apply ext_rel, antisym.
    + kat.
    + intros x y H.
      apply simpl_trt_hyp in H as [H1 [H2 H3]].
      exists y; try (split; auto).
      exists x; try (split; auto).
      simpl_trt; auto.
      * apply Hinc in H1.
        rewrite simpl_evts_be in H1.
        apply in_intersection in H1 as [_ H1]. unfold In in H1. unfold NLE; auto.
      * apply Hinc in H3.
        rewrite simpl_evts_be in H3.
        apply in_intersection in H3 as [_ H3]. unfold In in H3. unfold NLE; auto.
  - rewrite Hrf. rew bounded.
    apply ext_rel, antisym.
    + kat.
    + intros x y H.
      apply simpl_trt_hyp in H as [H1 [H2 H3]].
      exists y; try (split; auto).
      exists x; try (split; auto).
      simpl_trt; auto.
      * apply Hinc in H1.
        rewrite simpl_evts_be in H1.
        apply in_intersection in H1 as [_ H1]. unfold In in H1. unfold NLE; auto.
      * apply Hinc in H3.
        rewrite simpl_evts_be in H3.
        apply in_intersection in H3 as [_ H3]. unfold In in H3. unfold NLE; auto.
  - rewrite Hmo. rew bounded.
    apply ext_rel, antisym.
    + kat.
    + intros x y H.
      apply simpl_trt_hyp in H as [H1 [H2 H3]].
      exists y; try (split; auto).
      exists x; try (split; auto).
      simpl_trt; auto.
      * apply Hinc in H1.
        rewrite simpl_evts_be in H1.
        apply in_intersection in H1 as [_ H1]. unfold In in H1. unfold NLE; auto.
      * apply Hinc in H3.
        rewrite simpl_evts_be in H3.
        apply in_intersection in H3 as [_ H3]. unfold In in H3. unfold NLE; auto.
  - rewrite Hrmw. rew bounded.
    apply ext_rel, antisym.
    + kat.
    + intros x y H.
      apply simpl_trt_hyp in H as [H1 [H2 H3]].
      exists y; try (split; auto).
      exists x; try (split; auto).
      simpl_trt; auto.
      * apply Hinc in H1.
        rewrite simpl_evts_be in H1.
        apply in_intersection in H1 as [_ H1]. unfold In in H1. unfold NLE; auto.
      * apply Hinc in H3.
        rewrite simpl_evts_be in H3.
        apply in_intersection in H3 as [_ H3]. unfold In in H3. unfold NLE; auto.
Qed.


Lemma I_NLE (n: nat):
  [I (fun x => n >= numbering x)] = [NLE n].
Proof.
  apply ext_rel, antisym; intros x y H.
  - destruct H as [Heq Ht]. unfold I, In in Ht.
    split; auto.
  - destruct H as [Heq Ht]. unfold NLE in Ht.
    split; auto.
Qed.

(*
Lemma prefix_res_bminone (ex res: Execution) (bound: nat) (j k: Event):
  complete_exec ex ->
  rc11_consistent ex ->
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  is_read k ->
  ~(sc_consistent (bounded_exec ex bound)) ->
  sb_closed_restriction (bounded_exec ex bound) res (sbrf_before_jk ex bound j k) ->
  prefix (bounded_exec res (bound-1)) (bounded_exec ex (bound-1)).
Proof.
  intros Hcomp Hrc11 Hnumco Hmcp Hord Hkw Hnotsc Hres.
  inversion Hcomp as [Hval _].
  eapply (res_of_bound _ _ _ _ Hnumco) in Hres as Hres2.
  pose proof (prefix_res_ex _ _ _ _ _ Hcomp Hrc11 Hnumco Hmcp Hord Hres2) as Hpre.
  destruct_res Hres.
  repeat (apply conj).
  - rewrite 2simpl_evts_be, Hevts.
    intros x H.
    apply in_intersection in H as [H1 H2].
    apply Hinc in H1. rewrite simpl_evts_be in H1.
    apply in_intersection in H1 as [H1 _]. split; unfold In in *; auto.
  - intros a b Hsbrf Hin.
    unfold In in Hin. rew bounded in Hin. rewrite simpl_evts_be in Hin.
    apply in_intersection in Hin as [Heresb Heb].
    rewrite Hevts in Heresb. unfold In in *.
    rewrite simpl_evts_be. split.
    + rewrite Hevts. unfold sbrf_before_jk.
      destruct Heresb as [Heresb|Heresb]; unfold In.
      * left. apply rtc_inv_dcmp2. exists b; auto.
        apply (incl_rel_thm Hsbrf).
        rew bounded. rewrite NLE_bound_min_one. kat.
      * right. apply rtc_inv_dcmp2. exists b; auto.
        apply (incl_rel_thm Hsbrf).
        rew bounded. rewrite NLE_bound_min_one. kat.
    + unfold In.
      destruct Hsbrf as [Hsbrf|Hsbrf]; rew bounded in Hsbrf;
      apply simpl_trt_rel in Hsbrf.
      * apply (sb_num_ord _ _ _ Hnumco) in Hsbrf. lia.
      * apply (rf_num_ord _ _ _ Hnumco) in Hsbrf. lia.
  - rew bounded. rewrite Hsb. rew bounded. rewrite simpl_evts_be.
    rewrite Hevts. rewrite I_inter. rewrite I_NLE.
    apply ext_rel, antisym.
    + kat.
    + rewrite <-(NLE_bound_min_one bound). kat.
  - rew bounded. rewrite Hrf. rew bounded. rewrite simpl_evts_be.
    rewrite Hevts. rewrite I_inter. rewrite I_NLE.
    apply ext_rel, antisym.
    + kat.
    + rewrite <-(NLE_bound_min_one bound). kat.
  - rew bounded. rewrite Hmo. rew bounded. rewrite simpl_evts_be.
    rewrite Hevts. rewrite I_inter. rewrite I_NLE.
    apply ext_rel, antisym.
    + kat.
    + rewrite <-(NLE_bound_min_one bound). kat.
  - rew bounded. rewrite Hrmw. rew bounded. rewrite simpl_evts_be.
    rewrite Hevts. rewrite I_inter. rewrite I_NLE.
    apply ext_rel, antisym.
    + kat.
    + rewrite <-(NLE_bound_min_one bound). kat.
Qed.
*)

(** We chan the read event [k] to a new read event [n] that now reads its value
from the write event [c] *)

Definition change_val_read_k (ex1 ex2: Execution) (k c n: Event) (l: Loc) (v: Val) :=
  is_read k /\
  is_write c /\
  In _ (evts ex1) k /\
  In _ (evts ex1) c /\
  numbering c < numbering k /\
  Some l = get_loc k /\
  Some l = get_loc c /\
  Some v = get_val c /\
  n = Read (numbering k) (get_mode k) l v /\
  (* numbering ex1 n = numbering ex1 k /\ *)
  evts ex2 = Union _ (evts (bounded_exec ex1 ((numbering k)-1)))
                     (fun x => x = n) /\
  sb ex2 = (sb (bounded_exec ex1 ((numbering k)-1))) ⊔
           (fun x y => (sb ex1) x k /\ y = n) /\
  rmw ex2 = rmw (bounded_exec ex1 ((numbering k)-1)) /\
  rf ex2 = (rf (bounded_exec ex1 ((numbering k)-1))) ⊔
           (fun x y => x = c /\ y = n) /\
  mo ex2 = mo (bounded_exec ex1 ((numbering k)-1)).

Lemma change_val_read_exists (ex1: Execution) (k c: Event) (l: Loc) (v: Val):
  is_read k ->
  is_write c ->
  In _ (evts ex1) k ->
  In _ (evts ex1) c ->
  Some l = get_loc k ->
  Some l = get_loc c ->
  Some v = get_val c ->
  numbering c < numbering k ->
  exists ex2 n, change_val_read_k ex1 ex2 k c n l v.
Proof.
  pose (Read (get_eid k) (get_mode k) l v) as n.
  exists (mkex (Union _ (evts (bounded_exec ex1 ((numbering k)-1)))
                        (fun x => x = n))
               ((sb (bounded_exec ex1 ((numbering k)-1))) ⊔
                (fun x y => (sb ex1) x k /\ y = n))
              (rmw (bounded_exec ex1 ((numbering k)-1)))
              ((rf (bounded_exec ex1 ((numbering k)-1))) ⊔
               (fun x y => x = c /\ y = n))
              (mo (bounded_exec ex1 ((numbering k)-1)))).
  exists n.
  unfold change_val_read_k; intuition auto.
Qed.

Ltac inversion_chval H :=
  let Hkread := fresh "Hkread" in
  let Hcwrite := fresh "Hcwrite" in
  let Hink := fresh "Hink" in
  let Hinc := fresh "Hinc" in
  let Hordkc := fresh "Hordkc" in
  let Hloc := fresh "Hloc" in
  let Hsameloc := fresh "Hsameloc" in
  let Hval := fresh "Hval" in
  let Hn := fresh "Hn" in
  (* let Hnum := fresh "Hnum" in *)
  let Hevts := fresh "Hevts" in
  let Hsb := fresh "Hsb" in
  let Hrmw := fresh "Hrmw" in
  let Hrf := fresh "Hrf" in
  let Hmo := fresh "Hmo" in
  inversion H as [Hkread [Hcwrite [Hink [Hinc [Hordck [Hloc [Hsameloc [Hval [Hn 
                  [Hevts [Hsb [Hrmw [Hrf Hmo]]]]]]]]]]]]].

Lemma change_val_numco (ex1 ex2: Execution) (j k c n: Event) (bound: nat) (l: Loc) (v: Val):
  numbering_coherent ex1 ->
  change_val_read_k ex1 ex2 k c n l v ->
  numbering_coherent ex2.
Proof.
  intros Hnumco Hchval.
  inversion_chval Hchval.
  intros x y [Hxy|Hxy].
  - rewrite Hsb in Hxy. destruct Hxy as [Hxy|[Hx Hy]].
    * apply simpl_trt_rel in Hxy. apply Hnumco. left. auto.
    * apply (sb_num_ord _ _ _ Hnumco) in Hx.
      rewrite Hn in Hy. rewrite Hy. simpl. lia.
  - rewrite Hrf in Hxy. destruct Hxy as [Hxy|[Hx Hy]].
    * apply simpl_trt_rel in Hxy. apply Hnumco. right. auto.
    * rewrite Hx, Hy, Hn. simpl. lia.
Qed.

Lemma change_val_numinj (ex1 ex2: Execution) (j k c n: Event) (bound: nat) (l: Loc) (v: Val):
  numbering_injective ex1 ->
  change_val_read_k ex1 ex2 k c n l v ->
  numbering_injective ex2.
Proof.
  intros Hnuminj Hchval.
  split; intros H; apply Hnuminj; auto.
Qed.

Lemma change_val_valid (ex1 ex2: Execution) (j k c n: Event) (bound: nat) (l: Loc) (v: Val):
  valid_exec ex1 ->
  numbering_coherent ex1 ->
  change_val_read_k ex1 ex2 k c n l v ->
  valid_exec ex2.
Proof.
  intros Hval Hnumco Hchval.
  apply (bounded_is_valid _ (numbering k -1)) in Hval as Hvalpre; auto.
(*   inversion Hcomp as [Hval _]. *)
(*   inversion Hcompre as [Hvalpre _]. *)
  inversion_chval Hchval.
  split;[|split;[|split;[|split]]].
  - unfold valid_evts. apply conj.
    + intros e1 e2 Hin1 Hin2.
      rewrite Hevts in Hin1, Hin2.
      apply in_union in Hin1 as [Hin1|Hin1];
      apply in_union in Hin2 as [Hin2|Hin2].
      * destruct_val_exec Hvalpre.
        destruct Hevts_v as [Hevts_v _]. auto.
      * destruct_val_exec Hval. destruct Hevts_v as [Hevts_v _].
        apply in_intersection in Hin1 as [Hin1 Hnume1].
        destruct (Hevts_v _ _ Hin1 Hink) as [H|H].
        -- left. unfold In in Hin2. rewrite Hin2, Hn. cbn. auto.
        -- rewrite H in Hnume1. unfold In in Hnume1. lia.
      * destruct_val_exec Hval. destruct Hevts_v as [Hevts_v _].
        apply in_intersection in Hin2 as [Hin2 Hnume2].
        destruct (Hevts_v _ _ Hin2 Hink) as [H|H].
        -- left. unfold In in Hin1. rewrite Hin1, Hn. cbn. auto.
        -- rewrite H in Hnume2. unfold In in Hnume2. lia.
      * unfold In in Hin1, Hin2. right. rewrite Hin1, Hin2. auto.
    + intros e Hin.
      rewrite Hevts in Hin.
      apply in_union in Hin as [Hin|Hin].
      * destruct_val_exec Hvalpre.
        apply Hevts_v in Hin. auto.
      * unfold In in Hin. rewrite Hin, Hn.
        unfold valid_mode.
        apply Hval in Hink.
        unfold valid_mode in Hink.
        destruct k; simpl in Hkread; intuition auto.
  - rewrite Hevts, Hsb. repeat (apply conj).
    + apply ext_rel, antisym.
      * intros x y Hr.
        exists y. exists x.
        -- split; auto.
           destruct Hr as [Hr|[Hr _]].
           ++ rewrite simpl_sb_be in Hr.
              apply simpl_trt_hyp in Hr as [Hx [Hxsb _]].
              destruct_val_exec Hval.
              destruct_sb_v Hsb_v. destruct Hsb_lso as [[Hsb_lso _] _].
              left. rewrite simpl_evts_be. split.
              ** rewrite Hsb_lso in Hxsb. apply simpl_trt_hyp in Hxsb as [Hxsb _].
                 unfold I in Hxsb. auto.
              ** unfold NLE in Hx. unfold In. auto.
           ++ left. rewrite simpl_evts_be.
              split.
              ** destruct_val_exec Hval.
                 destruct_sb_v Hsb_v. destruct Hsb_lso as [[Hsb_lso _] _].
                 rewrite Hsb_lso in Hr. apply simpl_trt_hyp in Hr as [Hr _].
                 unfold I in Hr. auto.
              ** apply sb_num_ord in Hr. unfold In. lia. auto.
        -- auto.
        -- split; auto.
           destruct Hr as [Hr|[_ Hr]].
           ++ rewrite simpl_sb_be in Hr.
              apply simpl_trt_hyp in Hr as [_ [Hysb Hy]].
              destruct_val_exec Hval.
              destruct_sb_v Hsb_v. destruct Hsb_lso as [[Hsb_lso _] _].
              left. rewrite simpl_evts_be. split.
              ** rewrite Hsb_lso in Hysb. 
                 apply simpl_trt_hyp in Hysb as [_ [_ Hysb]].
                 unfold I in Hysb. auto.
              ** unfold NLE in Hy. unfold In. auto.
           ++ right. unfold In. auto.
      * intros x y H. apply simpl_trt_rel in H. auto.
    + inversion Hval as [_ [Hsb_v _]].
      destruct Hvalpre as [_ [Hsbpre_v _]].
      destruct Hsb_v as [[[_ [Hsbt _]] _] _].
      destruct Hsbpre_v as [[[_ [Hsbpret _]] _] _].
      intros x y [z [H1|[H1 H3]] [H2|[H2 H4]]].
      * left. apply Hsbpret. exists z; auto.
      * right. rew bounded in H1. apply simpl_trt_rel in H1.
        split; auto. apply Hsbt. exists z; auto.
      * left. rew bounded in H2. apply simpl_trt_hyp in H2 as [H2 _].
        rewrite H3 in H2. unfold NLE in H2.
        rewrite Hn in H2. simpl in H2. lia.
      * right. split; auto.
    + intros x [H|[H Heq]].
      * destruct_val_exec Hvalpre.
        destruct_sb_v Hsb_v.
        destruct Hsb_lso as [[_ [_ Hsb_lso]] _].
        eapply Hsb_lso. eauto.
      * destruct_val_exec Hval.
        destruct_sb_v Hsb_v.
        destruct Hsb_lso as [[H1 [_ H2]] _].
        rewrite H1 in H.
        apply simpl_trt_hyp in H as [Hx [H Hk]].
        destruct Hevts_v as [Hevts_v _].
        destruct (Hevts_v _ _ Hx Hk) as [Hnot|Hnot].
        -- rewrite Heq in Hnot. rewrite Hn in Hnot. cbn in Hnot. auto.
        -- apply (H2 k). rewrite Hnot in H. auto.
    + intros x y Hdiff Hin1 Hin2.
      apply in_union in Hin1 as [Hin1|Hin1];
      apply in_union in Hin2 as [Hin2|Hin2].
      * destruct_val_exec Hvalpre.
        destruct_sb_v Hsb_v. destruct Hsb_lso as [_ Htot].
        destruct (Htot _ _ Hdiff Hin1 Hin2).
        -- left; left; auto.
        -- right; left; auto.
      * unfold In in Hin2.
        rewrite simpl_evts_be in Hin1.
        apply in_intersection in Hin1 as [Hin1 Hnume1].
        destruct_val_exec Hval. destruct_sb_v Hsb_v.
        destruct Hsb_lso as [_ Htot].
        destruct (classic (x = k)) as [Hxk|Hxk].
        { rewrite Hxk in Hnume1. unfold In in Hnume1. lia. }
        destruct (Htot _ _ Hxk Hin1 Hink) as [Hsbxk|Hsbxk].
        -- left; right. apply conj; auto.
        -- apply sb_num_ord in Hsbxk. unfold In in Hnume1. lia. auto.
      * unfold In in Hin1.
        rewrite simpl_evts_be in Hin2.
        apply in_intersection in Hin2 as [Hin2 Hnume2].
        destruct_val_exec Hval. destruct_sb_v Hsb_v.
        destruct Hsb_lso as [_ Htot].
        destruct (classic (y = k)) as [Hyk|Hyk].
        { rewrite Hyk in Hnume2. unfold In in Hnume2. lia. }
        destruct (Htot _ _ Hyk Hin2 Hink) as [Hsbyk|Hsbyk].
        -- right; right. apply conj; auto.
        -- apply sb_num_ord in Hsbyk. unfold In in Hnume2. lia. auto.
      * unfold In in Hin1, Hin2. rewrite Hin1, Hin2 in Hdiff. intuition auto.
    + intros l2.
      destruct_val_exec Hval. destruct_sb_v Hsb_v.
      destruct (Hsbinit l2) as [e [Heloc [Heval [Heinit Hebef]]]].
      exists e; repeat (apply conj); auto.
      * intros Hnot. destruct Hnot as [z [Hnot|[Hnot Hnoteq]]].
        -- rew bounded in Hnot. apply simpl_trt_rel in Hnot.
           apply Heinit. exists z. auto.
        -- assert (In _ (ran (sb ex1)) k) as Hkran. { exists z; auto. }
           apply Hebef in Hkran. rewrite Hnoteq in Hkran.
           apply sb_num_ord in Hkran. rewrite Hn in Hkran. simpl in Hkran. lia. auto.
      * intros e' [z [Hin|[Hin1 Hin2]]].
        -- left. apply simpl_trt_hyp in Hin as [_ [Hze' He']].
           assert (In _ (ran (sb ex1)) e') as He'ran. { exists z; auto. }
           apply Hebef in He'ran. rew bounded; simpl_trt; auto.
           apply sb_num_ord in He'ran. unfold NLE in *. lia. auto.
        -- right. split; auto.
           assert (In _ (ran (sb ex1)) k) as He'ran. { exists z; auto. }
           apply Hebef in He'ran. auto.
  - apply conj.
    + intros r w Hrw. rewrite Hrmw in Hrw.
      destruct_val_exec Hval. destruct Hrmw_v as [Hrmw_v _].
      apply simpl_trt_hyp in Hrw as [Hrnum [Hrw Hwnum]].
      apply Hrmw_v in Hrw. unfold valid_rmw_pair.
      unfold valid_rmw_pair in Hrw.
      destruct (get_mode r); destruct (get_mode w); auto.
      * destruct Hrw as [Hread [Hwrite [Hlocrw Himmsb]]].
        repeat (apply conj); auto.
        -- rewrite Hsb. left. rew bounded. simpl_trt.
           destruct Himmsb. auto.
        -- { intros z Hzw. rewrite Hsb. rewrite Hsb in Hzw.
             destruct Hzw as [Hzw|Hzw].
             - destruct Himmsb as [Hrw1 Himmrw1].
               apply simpl_trt_hyp in Hzw as [Hznum [Hzw _]].
               apply Himmrw1 in Hzw as [Hzw1 Hzw2].
               split.
               + destruct Hzw1.
                 * left. left. rew bounded. simpl_trt. auto.
                 * right. auto.
               + intros z1 [H|H].
                 * apply simpl_trt_hyp in H as [H1 [H2 H3]].
                   apply Hzw2 in H2. destruct H2.
                   -- left. left. rew bounded. simpl_trt. auto.
                   -- right. auto.
                 * destruct H as [H1 H2]. apply Hzw2 in H1.
                   destruct H1.
                   -- left. right. split; auto.
                   -- simpl in H. rewrite H in Hwrite.
                      destruct k; unfold is_write, is_read in *; intuition auto.
             - destruct Hzw as [Hzk Hwn].
               rewrite Hwn in Hwrite. rewrite Hn in Hwrite.
               unfold is_write in Hwrite; intuition auto.
           }
      * destruct Hrw as [Hread [Hwrite [Hlocrw Himmsb]]].
        repeat (apply conj); auto.
        -- rewrite Hsb. left. rew bounded. simpl_trt.
           destruct Himmsb. auto.
        -- { intros z Hzw. rewrite Hsb. rewrite Hsb in Hzw.
             destruct Hzw as [Hzw|Hzw].
             - destruct Himmsb as [Hrw1 Himmrw1].
               apply simpl_trt_hyp in Hzw as [Hznum [Hzw _]].
               apply Himmrw1 in Hzw as [Hzw1 Hzw2].
               split.
               + destruct Hzw1.
                 * left. left. rew bounded. simpl_trt. auto.
                 * right. auto.
               + intros z1 [H|H].
                 * apply simpl_trt_hyp in H as [H1 [H2 H3]].
                   apply Hzw2 in H2. destruct H2.
                   -- left. left. rew bounded. simpl_trt. auto.
                   -- right. auto.
                 * destruct H as [H1 H2]. apply Hzw2 in H1.
                   destruct H1.
                   -- left. right. split; auto.
                   -- simpl in H. rewrite H in Hwrite.
                      destruct k; unfold is_write, is_read in *; intuition auto.
             - destruct Hzw as [Hzk Hwn].
               rewrite Hwn in Hwrite. rewrite Hn in Hwrite.
               unfold is_write in Hwrite; intuition auto.
           }               
      * destruct Hrw as [Hread [Hwrite [Hlocrw Himmsb]]].
        repeat (apply conj); auto.
        -- rewrite Hsb. left. rew bounded. simpl_trt.
           destruct Himmsb. auto.
        -- { intros z Hzw. rewrite Hsb. rewrite Hsb in Hzw.
             destruct Hzw as [Hzw|Hzw].
             - destruct Himmsb as [Hrw1 Himmrw1].
               apply simpl_trt_hyp in Hzw as [Hznum [Hzw _]].
               apply Himmrw1 in Hzw as [Hzw1 Hzw2].
               split.
               + destruct Hzw1.
                 * left. left. rew bounded. simpl_trt. auto.
                 * right. auto.
               + intros z1 [H|H].
                 * apply simpl_trt_hyp in H as [H1 [H2 H3]].
                   apply Hzw2 in H2. destruct H2.
                   -- left. left. rew bounded. simpl_trt. auto.
                   -- right. auto.
                 * destruct H as [H1 H2]. apply Hzw2 in H1.
                   destruct H1.
                   -- left. right. split; auto.
                   -- simpl in H. rewrite H in Hwrite.
                      destruct k; unfold is_write, is_read in *; intuition auto.
             - destruct Hzw as [Hzk Hwn].
               rewrite Hwn in Hwrite. rewrite Hn in Hwrite.
               unfold is_write in Hwrite; intuition auto.
           }        
      * destruct Hrw as [Hread [Hwrite [Hlocrw Himmsb]]].
        repeat (apply conj); auto.
        -- rewrite Hsb. left. rew bounded. simpl_trt.
           destruct Himmsb. auto.
        -- { intros z Hzw. rewrite Hsb. rewrite Hsb in Hzw.
             destruct Hzw as [Hzw|Hzw].
             - destruct Himmsb as [Hrw1 Himmrw1].
               apply simpl_trt_hyp in Hzw as [Hznum [Hzw _]].
               apply Himmrw1 in Hzw as [Hzw1 Hzw2].
               split.
               + destruct Hzw1.
                 * left. left. rew bounded. simpl_trt. auto.
                 * right. auto.
               + intros z1 [H|H].
                 * apply simpl_trt_hyp in H as [H1 [H2 H3]].
                   apply Hzw2 in H2. destruct H2.
                   -- left. left. rew bounded. simpl_trt. auto.
                   -- right. auto.
                 * destruct H as [H1 H2]. apply Hzw2 in H1.
                   destruct H1.
                   -- left. right. split; auto.
                   -- simpl in H. rewrite H in Hwrite.
                      destruct k; unfold is_write, is_read in *; intuition auto.
             - destruct Hzw as [Hzk Hwn].
               rewrite Hwn in Hwrite. rewrite Hn in Hwrite.
               unfold is_write in Hwrite; intuition auto.
           }
      * destruct Hrw as [Hread [Hwrite [Hlocrw Himmsb]]].
        repeat (apply conj); auto.
        -- rewrite Hsb. left. rew bounded. simpl_trt.
           destruct Himmsb. auto.
        -- { intros z Hzw. rewrite Hsb. rewrite Hsb in Hzw.
             destruct Hzw as [Hzw|Hzw].
             - destruct Himmsb as [Hrw1 Himmrw1].
               apply simpl_trt_hyp in Hzw as [Hznum [Hzw _]].
               apply Himmrw1 in Hzw as [Hzw1 Hzw2].
               split.
               + destruct Hzw1.
                 * left. left. rew bounded. simpl_trt. auto.
                 * right. auto.
               + intros z1 [H|H].
                 * apply simpl_trt_hyp in H as [H1 [H2 H3]].
                   apply Hzw2 in H2. destruct H2.
                   -- left. left. rew bounded. simpl_trt. auto.
                   -- right. auto.
                 * destruct H as [H1 H2]. apply Hzw2 in H1.
                   destruct H1.
                   -- left. right. split; auto.
                   -- simpl in H. rewrite H in Hwrite.
                      destruct k; unfold is_write, is_read in *; intuition auto.
             - destruct Hzw as [Hzk Hwn].
               rewrite Hwn in Hwrite. rewrite Hn in Hwrite.
               unfold is_write in Hwrite; intuition auto.
           }
    + rewrite Hevts, Hrmw.
      apply ext_rel, antisym.
      * intros x y H.
        destruct_val_exec Hvalpre. destruct_rmw_v Hrmw_v.
        rewrite Hrmw_in_e in H. apply simpl_trt_hyp in H as [H1 [H2 H3]].
        simpl_trt; auto; unfold I; left; auto.
      * kat.
  - unfold valid_rf. repeat (apply conj).
    + intros w r Hwr. rewrite Hrf in Hwr.
      destruct Hwr as [Hwr|Hwr].
      * destruct_val_exec Hvalpre. destruct_rf_v Hrf_v.
        apply Hrfco in Hwr. auto.
      * destruct Hwr as [Hw Hr]. rewrite Hw, Hr, Hn. simpl.
        rewrite Hloc, Hval0. split; auto.
        rewrite <-Hloc, <-Hsameloc. auto.
    + rewrite Hevts, Hrf. apply ext_rel, antisym; try kat.
      intros x y [H|[H1 H2]].
      * destruct_val_exec Hvalpre. destruct_rf_v Hrf_v.
        rewrite Hrf_in_e in H. apply simpl_trt_hyp in H as [Hl [Hm Hr]].
        exists y. exists x.
        -- split. auto. apply in_union_l. auto.
        -- left. auto.
        -- split. auto. apply in_union_l. auto.
      * exists y. exists x.
        -- split. auto. apply in_union_l. rewrite H1.
           rewrite simpl_evts_be. split; auto.
           unfold In. lia.
        -- right. auto.
        -- split. auto. apply in_union_r. cbv. auto.
    + rewrite Hrf. apply ext_rel, antisym; try kat.
      intros x y [H|[H1 H2]].
      * destruct_val_exec Hvalpre. destruct_rf_v Hrf_v.
        rewrite <-Hrfwr in H.
        apply simpl_trt_hyp in H as [Hl [Hm Hr]].
        exists y. exists x.
        -- split; auto.
        -- left. auto.
        -- split; auto.
      * exists y. exists x.
        -- split; auto. rewrite H1.
           destruct c; unfold is_write in Hcwrite; intuition auto.
        -- right; auto.
        -- split; auto. rewrite H2, Hn. simpl. auto.
    + rewrite Hrf. intros w1 w2 r [[H1|[H1 H2]] [H3|[H3 H4]]].
      * destruct_val_exec Hvalpre. destruct_rf_v Hrf_v.
        eapply Hrfun. split; eauto.
      * rewrite H4 in H1.
        apply simpl_trt_rel in H1 as Hwn.
        apply (rf_dest_evts _ Hval) in Hwn.
        assert (n = k) as Hnk.
        { eapply (same_eid_same_evts ex1); eauto.
          rewrite Hn. cbn. auto. }
        apply (rf_dest_evts _ Hvalpre) in H1.
        rewrite Hnk in H1. rewrite simpl_evts_be in H1.
        apply in_intersection in H1 as [_ H1].
        unfold In in H1. lia.
      * rewrite H2 in H3.
        apply simpl_trt_rel in H3 as Hwn.
        apply (rf_dest_evts _ Hval) in Hwn.
        assert (n = k) as Hnk.
        { eapply (same_eid_same_evts ex1); eauto.
          rewrite Hn. cbn. auto. }
        apply (rf_dest_evts _ Hvalpre) in H3.
        rewrite Hnk in H3. rewrite simpl_evts_be in H3.
        apply in_intersection in H3 as [_ H3].
        unfold In in H3. lia.
      * rewrite H1, H3. auto.
  - rewrite Hevts, Hmo. unfold valid_mo.
    repeat (apply conj).
    + destruct_val_exec Hvalpre. destruct_mo_v Hmo_v. auto.
    + destruct_val_exec Hvalpre. destruct_mo_v Hmo_v. auto.
    + apply ext_rel, antisym; try kat.
      intros x y H.
      apply (mo_orig_evts _ Hvalpre) in H as Hxevts.
      apply (mo_dest_evts _ Hvalpre) in H as Hyevts.
      exists y. exists x.
      * split. auto. left. auto.
      * auto.
      * split. auto. left. auto.
    + destruct_val_exec Hvalpre. destruct_mo_v Hmo_v.
      destruct Hmopo as [_ [Hmopo _]]. auto.
    + destruct_val_exec Hvalpre. destruct_mo_v Hmo_v.
      destruct Hmopo as [_ [_ Hmopo]]. auto.
    + destruct_val_exec Hvalpre. destruct_mo_v Hmo_v.
      assert (forall s l, writes_loc (Union _ s (fun x => x =n)) l =
                          writes_loc s l).
      { intros s l0. apply ext_set. intros x. split; intros H.
        - unfold writes_loc in *. destruct H as [H1 [H2 H3]]; auto;
          repeat (apply conj); auto.
          apply in_union in H1 as [H1|H1]. auto.
          unfold In in H1. rewrite H1 in H2. rewrite Hn in H2.
          simpl in H2. intuition auto.
        - unfold writes_loc in *. destruct H as [H1 [H2 H3]];
          repeat (apply conj); auto.
          left. auto.
      }
      intros l0.
      rewrite (H (evts (bounded_exec ex1 (numbering k - 1))) l0).
      auto.
Qed.


Lemma change_val_complete (ex1 ex2: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  complete_exec ex1 ->
  numbering_coherent ex1 ->
  change_val_read_k ex1 ex2 k c n l v ->
  complete_exec ex2.
Proof.
  intros Hcomp Hnumco Hchval.
  inversion Hcomp as [Hval _].
  inversion_chval Hchval.
  apply conj.
  eapply change_val_valid; eauto.
  apply (bounded_is_complete _ (numbering k -1)) in Hcomp as Hcompre; auto.
  destruct Hcompre as [_ Hcompre].
  intros x H.
  rewrite Hevts in H. rewrite Hrf.
  unfold reads, In in H. destruct H as [H Hr].
  apply in_union in H as [H|H].
  - assert (In _ (reads (evts (bounded_exec ex1 (numbering k - 1)))) x) as H'.
    { split; auto. }
    apply Hcompre in H'. destruct H' as [y H'].
    exists y. left. auto.
  - exists c. right. split; intuition auto.
Qed.

Lemma change_val_atomicity (ex1 ex2: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  complete_exec ex1 ->
  rc11_consistent ex1 ->
  numbering_coherent ex1 ->
  numbering_injective ex1 ->
  minimal_conflicting_pair ex1 bound j k ->
  numbering k > numbering j ->
  change_val_read_k ex1 ex2 k c n l v ->
  atomicity ex2.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hchval.
  inversion_chval Hchval.
  intros x y Hnot. unfold rb in Hnot.
  rewrite Hrmw, Hrf, Hmo in Hnot.
  assert (sc_consistent (bounded_exec ex1 (numbering k - 1))) as Hsc.
  { destruct Hcomp as [Hvalid _].
    eapply smaller_than_smallest_sc; eauto.
    inversion Hmcp as [Hscb _].
    rewrite (mcp_num_snd_evt_ord _ _ _ _ Hvalid Hnumco Hmcp Hord).
    apply (mcp_bound_gt_zero _ _ _ _ Hnuminj) in Hmcp.
    assert (S (bound-1) = bound) as Hsimp. { lia. }
    rewrite Hsimp. auto.
  }
  destruct Hsc as [Hat _].
  apply (Hat x y).
  destruct Hnot as [H1 [z1 [z2 [H2|[H2 H2']] H3] H4]].
  - split; auto. exists z1; auto. exists z2; auto.
  - apply rmw_orig_evts in H1.
    + rewrite H2' in H1.
      rewrite simpl_evts_be in H1.
      apply in_intersection in H1 as [_ H1].
      unfold In in H1. rewrite Hn in H1. simpl in H1.
      lia.
    + destruct Hcomp. eauto using bounded_is_valid.
Qed.

Definition sb_closed_restriction (ex res: Execution) (e: Ensemble Event) :=
  Included _ e (evts ex) /\
  (forall a b, In _ e b -> (sb ex) a b -> In _ e a) /\
  evts res = e /\
  sb res = [I e]⋅sb ex⋅[I e] /\
  rf res = [I e]⋅rf ex⋅[I e] /\
  mo res = [I e]⋅mo ex⋅[I e] /\
  rmw res = [I e]⋅rmw ex⋅[I e].

Ltac destruct_res H :=
  let H1 := fresh "Hinc" in
  let H2 := fresh "Hclo" in
  let H3 := fresh "Hevts" in
  let H4 := fresh "Hsb" in
  let H5 := fresh "Hrf" in
  let H6 := fresh "Hmo" in
  let H7 := fresh "Hrmw" in
  destruct H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].

Ltac inversion_res H :=
  let H1 := fresh "Hinc" in
  let H2 := fresh "Hclo" in
  let H3 := fresh "Hevts" in
  let H4 := fresh "Hsb" in
  let H5 := fresh "Hrf" in
  let H6 := fresh "Hmo" in
  let H7 := fresh "Hrmw" in
  inversion H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].

Definition change_val_read_k (ex1 ex2: Execution) (k c n: Event) (l: Loc) (v: Val) :=
  is_read k /\
  is_write c /\
  In _ (evts ex1) k /\
  In _ (evts ex1) c /\
  numbering c < numbering k /\
  Some l = get_loc k /\
  Some l = get_loc c /\
  Some v = get_val c /\
  n = Read (numbering k) (get_mode k) l v /\
  evts ex2 = Union _ (evts (bounded_exec ex1 ((numbering k)-1)))
                     (fun x => x = n) /\
  sb ex2 = (sb (bounded_exec ex1 ((numbering k)-1))) ⊔
           (fun x y => (sb ex1) x k /\ y = n) /\
  rmw ex2 = rmw (bounded_exec ex1 ((numbering k)-1)) /\
  rf ex2 = (rf (bounded_exec ex1 ((numbering k)-1))) ⊔
           (fun x y => x = c /\ y = n) /\
  mo ex2 = mo (bounded_exec ex1 ((numbering k)-1)).
*)

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

Definition res_chval_k (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val) :=
  let n := Read (numbering k) (get_mode k) l v in
  let evts_int := sbrf_before_jk ex bound j k in
  let sb_int := [I evts_int]⋅sb ex⋅[I evts_int] in
  let rf_int := [I evts_int]⋅rf ex⋅[(I evts_int) ⊓ ((fun x => x <> k): prop_set Event)] in
  In _ evts_int c /\
  is_write c /\
  is_read k /\
  evts res = Union _  evts_int (id n) /\
  sb res = sb_int ⊔ (fun x y => sb_int x k /\ y = n) /\
  rmw res = [I evts_int]⋅rmw ex⋅[I evts_int]/\
  rf res =  rf_int ⊔ (fun x y => x = c /\ y = n)/\
  mo res = [I evts_int]⋅mo ex⋅[I evts_int].

Ltac destruct_res_chval H :=
  let H1 := fresh "Hinc" in
  let H2 := fresh "Hcw" in
  let H3 := fresh "Hkr" in
  let H4 := fresh "Hevts" in
  let H5 := fresh "Hsb" in
  let H6 := fresh "Hrmw" in
  let H7 := fresh "Hrf" in
  let H8 := fresh "Hmo" in
  destruct H as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].

Ltac inversion_res_chval H :=
  let H1 := fresh "Hinc" in
  let H2 := fresh "Hcw" in
  let H3 := fresh "Hkr" in
  let H4 := fresh "Hevts" in
  let H5 := fresh "Hsb" in
  let H6 := fresh "Hrmw" in
  let H7 := fresh "Hrf" in
  let H8 := fresh "Hmo" in
  inversion H as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].

Lemma numco_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  numbering_coherent ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma numinj_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  numbering_injective ex ->
  res_chval_k ex res bound j k c n l v ->
  numbering_injective res.
Proof.
  intros Hnuminj Hres. split; apply Hnuminj; auto.
Qed.


Lemma evts_res_sbrf_numbering_jk (ex res: Execution) (bound: nat) (j k c n x: Event) (l: Loc) (v: Val):
  numbering_injective ex ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma evts_v_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma sb_po_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  partial_order (sb ex) (evts ex) ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma sb_tot_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  total_rel (sb ex) (evts ex) ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma sb_lso_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  linear_strict_order (sb ex) (evts ex) ->
  res_chval_k ex res bound j k c n l v ->
  linear_strict_order (sb res) (evts res).
Proof.
  intros Hval Hnumco Hnuminj Hmcp Hord [Hpo Htot] Hres. apply conj.
  - eapply sb_po_res_chval; eauto.
  - eapply sb_tot_res_chval; eauto.
Qed.

Lemma sb_v_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma imm_sb_res_chval (ex res: Execution) (bound: nat) (j k c n r w: Event) (l: Loc) (v: Val):
  imm (sb ex) r w ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma rmw_v1_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma rmw_v2_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c n l v ->
  rmw res =  [I (evts res)]⋅rmw res⋅[I (evts res)].
Proof.
  intros Hval Hres. destruct_val_exec Hval. destruct_rmw_v Hrmw_v.
  destruct_res_chval Hres.
  rewrite Hevts, Hrmw. rewrite test_i_union. kat_eq.
Qed.

Lemma rmw_v_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c n l v ->
  valid_rmw (evts res) (sb res) (rmw res).
Proof.
  intros Hval Hres.
  split.
  - eapply rmw_v1_res_chval; eauto.
  - eapply rmw_v2_res_chval; eauto.
Qed.

Lemma rf_v1_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  get_loc c = Some l ->
  get_val c = Some v ->
  res_chval_k ex res bound j k c n l v ->
  (forall w r : Event, rf res w r -> get_loc w = get_loc r /\ get_val w = get_val r).
Proof.
  intros Hval Hcloc Hcval Hres w r Hwr. destruct_val_exec Hval. destruct_rf_v Hrf_v.
  destruct_res_chval Hres. rewrite Hrf in Hwr.
  destruct Hwr as [Hwr|[Hwr Heq]].
  - apply Hrfco. eapply simpl_trt_rel; eauto.
  - rewrite Hwr, Heq. split; auto.
Qed.

Lemma rf_v2_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma rf_v3_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c n l v ->
  [W]⋅rf res⋅[R] = rf res.
Proof.
  intros Hval Hres. destruct_res_chval Hres. destruct_val_exec Hval.
  destruct_rf_v Hrf_v.
  rewrite Hrf. rewrite <-Hrfwr at 2. rewrite (rf_res_chval_wr _ _ _ _ Hcw).
  kat_eq.
Qed.

Lemma rf_v4_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma rf_v_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  get_loc c = Some l ->
  get_val c = Some v ->
  res_chval_k ex res bound j k c n l v ->
  valid_rf (evts res) (rf res).
Proof.
  intros Hval Hnuminj Hcloc Hcval Hres. split;[|split;[|split]].
  - eapply rf_v1_res_chval; eauto.
  - eapply rf_v2_res_chval; eauto.
  - eapply rf_v3_res_chval; eauto.
  - eapply rf_v4_res_chval; eauto.
Qed.

Lemma mo_v1_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c n l v ->
  [W]⋅(mo res)⋅[W] = (mo res).
Proof.
  intros Hval Hres. destruct_res_chval Hres.
  rewrite Hmo. destruct_val_exec Hval. destruct_mo_v Hmo_v.
  rewrite <-Hmoww. kat_eq.
Qed.

Lemma mo_v2_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c n l v ->
  (forall x y, (mo res) x y -> get_loc x = get_loc y).
Proof.
  intros Hval Hres x y Hrel.
  destruct_val_exec Hval. destruct_mo_v Hmo_v.
  apply Hmosameloc. destruct_res_chval Hres.
  rewrite Hmo in Hrel. eapply simpl_trt_rel. eauto.
Qed.

Lemma mo_v3_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma writes_loc_res_chval (ex res: Execution) (bound: nat) (j k c n x: Event) (l l2: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma mo_v4_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma mo_v_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  res_chval_k ex res bound j k c n l v ->
  valid_mo (evts res) (mo res).
Proof.
  intros Hval Hnuminj Hmcp Hres.
  split;[|split;[|split]].
  - eapply mo_v1_res_chval; eauto.
  - eapply mo_v2_res_chval; eauto.
  - eapply mo_v3_res_chval; eauto.
  - eapply mo_v4_res_chval; eauto.
Qed.

Lemma valid_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  get_loc c = Some l ->
  get_val c = Some v ->
  res_chval_k ex res bound j k c n l v ->
  valid_exec res.
Proof.
  intros Hval Hnumco Hnuminj Hmcp Hord Hcloc Hcval Hres.
  split;[|split;[|split;[|split]]].
  - eapply evts_v_res_chval; eauto.
  - eapply sb_v_res_chval; eauto.
  - eapply rmw_v_res_chval; eauto.
  - eapply rf_v_res_chval; eauto.
  - eapply mo_v_res_chval; eauto.
Qed.

Lemma reads_in_rf_ran_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  res_chval_k ex res bound j k c n l v ->
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

Lemma complete_res_chval (ex res: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  complete_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  minimal_conflicting_pair ex bound j k ->
  numbering k > numbering j ->
  get_loc c = Some l ->
  get_val c = Some v ->
  res_chval_k ex res bound j k c n l v ->
  complete_exec res.
Proof.
  intros Hcomp Hnumco Hnuminj Hmcp Hord Hcloc Hcval Hres.
  inversion Hcomp as [Hval Hrfran].
  split.
  - eapply valid_res_chval; eauto.
  - eapply reads_in_rf_ran_res_chval; eauto.
Qed.

(** Last write in the modification order for a given location *)

Definition max_mo (e: Event) (ex: Execution) (l: Loc) :=
  get_loc e = Some l /\
  In _ (writes (evts ex)) e /\
  forall x, In _ (evts ex) x ->
            get_loc x = Some l ->
            x <> e ->
            (mo ex) x e.

(** If the execution contains at least one write event to a location l, there 
exists at least on event that is the maximal element in the mo on this location l *)

Axiom exists_max_mo:
  forall ex l,
  (exists e, In _ (writes (evts ex)) e /\ get_loc e = Some l) ->
  exists e, max_mo e ex l.

Lemma change_val_eco_ac (ex1 ex2: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  complete_exec ex1 ->
  rc11_consistent ex1 ->
  numbering_coherent ex1 ->
  numbering_injective ex1 ->
  minimal_conflicting_pair ex1 bound j k ->
  numbering k > numbering j ->
  max_mo c ex1 l ->
  change_val_read_k ex1 ex2 k c n l v ->
  acyclic (sb ex2 ⊔ rf ex2 ⊔ mo ex2 ⊔ rb ex2).
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hmaxmo Hchval.
  inversion Hcomp as [Hval _].
  inversion_chval Hchval.
  assert (sc_consistent (bounded_exec ex1 (numbering k - 1))) as Hsc.
  { eapply smaller_than_smallest_sc; eauto.
    destruct Hcomp as [Hvalid _].
    inversion Hmcp as [Hscb _].
    rewrite (mcp_num_snd_evt_ord _ _ _ _ Hvalid Hnumco Hmcp Hord).
    apply (mcp_bound_gt_zero _ _ _ _ Hnuminj) in Hmcp.
    assert (S (bound-1) = bound) as Hsimp. { lia. }
    rewrite Hsimp. auto.
  }
  destruct Hsc as [_ Hac].
  intros x Hnot.
  apply (Hac x).
  unfold rb in Hnot.
  rewrite Hsb, Hrf, Hmo in Hnot.
  exfalso. 
  assert ((sb (bounded_exec ex1 (numbering k - 1 )) ⊔
           (fun x y => sb ex1 x k /\ y = n) ⊔
           (rf (bounded_exec ex1 (numbering k - 1)) ⊔
            (fun x y => x = c /\ y = n)) ⊔
           mo (bounded_exec ex1 (numbering k - 1)) ⊔
           (rf (bounded_exec ex1 (numbering k - 1)) ⊔ 
            (fun x y => x = c /\ y = n))° ⋅ 
            mo (bounded_exec ex1 (numbering k - 1))) ≦
          ((sb (bounded_exec ex1 (numbering k - 1)) ⊔
            rf (bounded_exec ex1 (numbering k - 1)) ⊔
            mo (bounded_exec ex1 (numbering k - 1)) ⊔
            ((rf (bounded_exec ex1 (numbering k - 1)))° ⋅
             mo (bounded_exec ex1 (numbering k - 1)))) ⊔
           (((fun x y => sb ex1 x k /\ y = n): rlt Event) ⊔
            (fun x y => x = c /\ y = n) ⊔
            (((fun x y => x = c /\ y = n): rlt Event)° ⋅ mo (bounded_exec ex1 (numbering k - 1)))
          ))) as H.
  { intros z1 z2 [[[[H | H] | H] | H] | H];
    try (apply (incl_rel_thm H); kat).
    - right. left. left. auto.
    - destruct H as [z3 H1 H2].
      rewrite <-cnv_rev in H1. destruct H1 as [H1|H1].
      + left. right. exists z3; auto.
      + right. right. exists z3; auto.
  }
  apply (tc_incl _ _ H) in Hnot. clear H.
  unfold rb, acyclic in Hac.
  apply (path_impl_pass_through _ _ _ _ (Hac x)) in Hnot.
  destruct Hnot as [z1 [z2 Hbeg Hmid] Hend].
  destruct Hmid as [Hmid _ (* Hnotmid*)].
  rewrite rtc_inv_dcmp6 in Hbeg. rewrite rtc_inv_dcmp6 in Hend.
  rewrite tc_inv_dcmp2 in Hbeg. rewrite tc_inv_dcmp2 in Hend.
  destruct Hbeg as [Hbeg|[z3 Hbeg1 _]];
  destruct Hend as [Hend|[z4 Hend1 _]].
  - simpl in Hbeg. simpl in Hend.
    destruct Hmid as [[Hmid|Hmid]|Hmid].
    + destruct Hmid as [Hxk Heqx].
      rewrite <-Hbeg, <-Hend, Heqx in Hxk.
      apply (sb_num_ord _ _ _ Hnumco) in Hxk.
      rewrite Hn in Hxk. simpl in Hxk. lia.
    + destruct Hmid as [Hxc Hxn]. 
      rewrite Hend, Hbeg, Hxc in Hxn.
      rewrite Hxn in Hcwrite. rewrite Hn in Hcwrite.
      simpl in Hcwrite. destruct Hcwrite.
    + destruct Hmid as [z3 Hmid1 Hmid2].
      rewrite <-cnv_rev in Hmid1. rew bounded in Hmid2.
      destruct Hmid1 as [Hmid11 Hmid12]. rewrite Hend, Hbeg, Hmid12 in Hmid2.
      apply simpl_trt_tright in Hmid2. unfold NLE in Hmid2.
      rewrite Hn in Hmid2. simpl in Hmid2. lia.
  - destruct Hmid as [[Hmid|Hmid]|Hmid].
    + destruct Hmid as [_ Hmid].
      destruct Hend1 as [[[[Hend1|Hend1]|Hend1]|Hend1]|[[Hend1|Hend1]|Hend1]].
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * destruct Hend1 as [z5 Hend11 Hend12]. rewrite <-cnv_rev in Hend11.
        rew bounded in Hend11. apply simpl_trt_tright in Hend11.
        rewrite Hmid in Hend11. unfold NLE in Hend11. rewrite Hn in Hend11.
        simpl in Hend11. lia.
      * destruct Hend1 as [Hend1 _]. rewrite Hmid in Hend1.
        apply (sb_num_ord _ _ _ Hnumco) in Hend1. rewrite Hn in Hend1.
        simpl in Hend1. lia.
      * destruct Hend1 as [Hend1 _]. rewrite Hend1 in Hmid.
        rewrite Hmid in Hcwrite. rewrite Hn in Hcwrite. simpl in Hcwrite. destruct Hcwrite.
      * destruct Hend1 as [z5 Hend11 Hend12]. rewrite <-cnv_rev in Hend11.
        destruct Hend11 as [Hend11 _].
        destruct Hmaxmo as [_ Hmaxmo]. rew bounded in Hend12.
        apply simpl_trt_hyp in Hend12 as [_ [Hend12 _]]. rewrite Hend11 in Hend12.
        inversion Hcomp as [Hvalid _].
        apply (mo_dest_evts _ Hvalid) in Hend12 as Hz4evts.
        apply (mo_same_loc _ Hvalid) in Hend12 as Hsloc.
        rewrite <-Hsameloc in Hsloc.
        destruct (classic (z4 = c)) as [H|H].
        { rewrite H in Hend12.
          pose proof (mo_irr _ Hval) as Hmoirr.
          rewrite <-irreflexive_is_irreflexive in Hmoirr.
          apply (Hmoirr c); auto. }
        apply Hmaxmo in Hz4evts; auto.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). destruct_val_exec Hvalid.
        destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
        apply Hmotrans. exists z4; auto.
    + destruct Hmid as [_ Hmid].
      destruct Hend1 as [[[[Hend1|Hend1]|Hend1]|Hend1]|[[Hend1|Hend1]|Hend1]].
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * destruct Hend1 as [z5 Hend11 Hend12]. rewrite <-cnv_rev in Hend11.
        rew bounded in Hend11. apply simpl_trt_tright in Hend11.
        rewrite Hmid in Hend11. unfold NLE in Hend11. rewrite Hn in Hend11.
        simpl in Hend11. lia.
      * destruct Hend1 as [Hend1 _]. rewrite Hmid in Hend1.
        apply (sb_num_ord _ _ _ Hnumco) in Hend1. rewrite Hn in Hend1. 
        simpl in Hend1. lia.
      * destruct Hend1 as [Hend1 _]. rewrite Hend1 in Hmid.
        rewrite Hmid in Hcwrite. rewrite Hn in Hcwrite. simpl in Hcwrite. destruct Hcwrite.
      * destruct Hend1 as [z5 Hend11 Hend12]. rewrite <-cnv_rev in Hend11.
        destruct Hend11 as [Hend11 _].
        destruct Hmaxmo as [_ Hmaxmo]. rew bounded in Hend12.
        apply simpl_trt_hyp in Hend12 as [_ [Hend12 _]]. rewrite Hend11 in Hend12.
        inversion Hcomp as [Hvalid _].
        apply (mo_dest_evts _ Hvalid) in Hend12 as Hz4evts.
        apply (mo_same_loc _ Hvalid) in Hend12 as Hsloc.
        rewrite <-Hsameloc in Hsloc.
        destruct (classic (z4 = c)) as [H|H].
        { rewrite H in Hend12.
          pose proof (mo_irr _ Hval) as Hmoirr.
          rewrite <-irreflexive_is_irreflexive in Hmoirr.
          apply (Hmoirr c); auto. }
        apply Hmaxmo in Hz4evts; auto.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). destruct_val_exec Hvalid.
        destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
        apply Hmotrans. exists z4; auto.
    + destruct Hmid as [z5 Hmid1 Hmid2]. rewrite <-cnv_rev in Hmid1.
      destruct Hmid1 as [Hz5c _]. apply simpl_trt_hyp in Hmid2 as [_ [Hmid2 _]].
      destruct Hmaxmo as [_ Hmaxmo]. inversion Hcomp as [Hvalid _].
      rewrite Hz5c in Hmid2.
      apply (mo_dest_evts _ Hvalid) in Hmid2 as Hz1evts.
      apply (mo_same_loc _ Hvalid) in Hmid2 as Hsloc.
      rewrite <-Hsameloc in Hsloc.
      destruct (classic (z1 = c)) as [H|H].
      { rewrite H in Hmid2.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). auto. }
      apply Hmaxmo in Hz1evts; auto.
      pose proof (mo_irr _ Hval) as Hmoirr.
      rewrite <-irreflexive_is_irreflexive in Hmoirr.
      apply (Hmoirr c). destruct_val_exec Hvalid.
      destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
      apply Hmotrans. exists z1; auto.
  - simpl in Hend. rewrite Hend in Hmid.
    destruct Hmid as [[Hmid|Hmid]|Hmid].
    + destruct Hmid as [_ Hmid].
      destruct Hbeg1 as [[[[Hbeg1|Hbeg1]|Hbeg1]|Hbeg1]|[[Hbeg1|Hbeg1]|Hbeg1]].
      * rewrite Hmid in Hbeg1. apply simpl_trt_hyp in Hbeg1 as [Hbeg1 _].
        unfold NLE in Hbeg1. rewrite Hn in Hbeg1. simpl in Hbeg1. lia.
      * rewrite Hmid in Hbeg1. apply simpl_trt_hyp in Hbeg1 as [Hbeg1 _].
        unfold NLE in Hbeg1. rewrite Hn in Hbeg1. simpl in Hbeg1. lia.
      * rewrite Hmid in Hbeg1. apply simpl_trt_hyp in Hbeg1 as [Hbeg1 _].
        unfold NLE in Hbeg1. rewrite Hn in Hbeg1. simpl in Hbeg1. lia.
      * destruct Hbeg1 as [z5 Hbeg11 Hbeg12]. rewrite <-cnv_rev in Hbeg11.
        rew bounded in Hbeg11. apply simpl_trt_tright in Hbeg11.
        rewrite Hmid in Hbeg11. unfold NLE in Hbeg11. rewrite Hn in Hbeg11.
        simpl in Hbeg11. lia.
      * destruct Hbeg1 as [Hbeg1 _]. rewrite Hmid in Hbeg1.
        apply (sb_num_ord _ _ _ Hnumco) in Hbeg1. rewrite Hn in Hbeg1. 
        simpl in Hbeg1. lia.
      * destruct Hbeg1 as [Hbeg1 _]. rewrite Hbeg1 in Hmid.
        rewrite Hmid in Hcwrite. rewrite Hn in Hcwrite. simpl in Hcwrite. destruct Hcwrite.
      * destruct Hbeg1 as [z5 Hbeg11 Hbeg12]. rewrite <-cnv_rev in Hbeg11.
        destruct Hbeg11 as [Hbeg11 _].
        destruct Hmaxmo as [_ Hmaxmo]. rew bounded in Hbeg12.
        apply simpl_trt_hyp in Hbeg12 as [_ [Hbeg12 _]]. rewrite Hbeg11 in Hbeg12.
        inversion Hcomp as [Hvalid _].
        apply (mo_dest_evts _ Hvalid) in Hbeg12 as Hz3evts.
        apply (mo_same_loc _ Hvalid) in Hbeg12 as Hsloc.
        rewrite <-Hsameloc in Hsloc.
        destruct (classic (z3 = c)) as [H|H].
        { rewrite H in Hbeg12.
          pose proof (mo_irr _ Hval) as Hmoirr.
          rewrite <-irreflexive_is_irreflexive in Hmoirr.
          apply (Hmoirr c); auto. }
        apply Hmaxmo in Hz3evts; auto.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). destruct_val_exec Hvalid.
        destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
        apply Hmotrans. exists z3; auto.
    + destruct Hmid as [_ Hmid].
      destruct Hbeg1 as [[[[Hbeg1|Hbeg1]|Hbeg1]|Hbeg1]|[[Hbeg1|Hbeg1]|Hbeg1]].
      * rewrite Hmid in Hbeg1. apply simpl_trt_hyp in Hbeg1 as [Hbeg1 _].
        unfold NLE in Hbeg1. rewrite Hn in Hbeg1. simpl in Hbeg1. lia.
      * rewrite Hmid in Hbeg1. apply simpl_trt_hyp in Hbeg1 as [Hbeg1 _].
        unfold NLE in Hbeg1. rewrite Hn in Hbeg1. simpl in Hbeg1. lia.
      * rewrite Hmid in Hbeg1. apply simpl_trt_hyp in Hbeg1 as [Hbeg1 _].
        unfold NLE in Hbeg1. rewrite Hn in Hbeg1. simpl in Hbeg1. lia.
      * destruct Hbeg1 as [z5 Hbeg11 Hbeg12]. rewrite <-cnv_rev in Hbeg11.
        rew bounded in Hbeg11. apply simpl_trt_tright in Hbeg11.
        rewrite Hmid in Hbeg11. unfold NLE in Hbeg11. rewrite Hn in Hbeg11.
        simpl in Hbeg11. lia.
      * destruct Hbeg1 as [Hbeg1 _]. rewrite Hmid in Hbeg1.
        apply (sb_num_ord _ _ _ Hnumco) in Hbeg1. rewrite Hn in Hbeg1. 
        simpl in Hbeg1. lia.
      * destruct Hbeg1 as [Hbeg1 _]. rewrite Hbeg1 in Hmid.
        rewrite Hmid in Hcwrite. rewrite Hn in Hcwrite. simpl in Hcwrite. destruct Hcwrite.
      * destruct Hbeg1 as [z5 Hbeg11 Hbeg12]. rewrite <-cnv_rev in Hbeg11.
        destruct Hbeg11 as [Hbeg11 _].
        destruct Hmaxmo as [_ Hmaxmo]. rew bounded in Hbeg12.
        apply simpl_trt_hyp in Hbeg12 as [_ [Hbeg12 _]]. rewrite Hbeg11 in Hbeg12.
        inversion Hcomp as [Hvalid _].
        apply (mo_dest_evts _ Hvalid) in Hbeg12 as Hz3evts.
        apply (mo_same_loc _ Hvalid) in Hbeg12 as Hsloc.
        rewrite <-Hsameloc in Hsloc.
        destruct (classic (z3 = c)) as [H|H].
        { rewrite H in Hbeg12.
          pose proof (mo_irr _ Hval) as Hmoirr.
          rewrite <-irreflexive_is_irreflexive in Hmoirr.
          apply (Hmoirr c); auto. }
        apply Hmaxmo in Hz3evts; auto.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). destruct_val_exec Hvalid.
        destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
        apply Hmotrans. exists z3; auto.
    + destruct Hmid as [z5 Hmid1 Hmid2]. rewrite <-cnv_rev in Hmid1.
      destruct Hmid1 as [Hz5c _]. apply simpl_trt_hyp in Hmid2 as [_ [Hmid2 _]].
      destruct Hmaxmo as [_ Hmaxmo]. inversion Hcomp as [Hvalid _].
      rewrite Hz5c in Hmid2.
      apply (mo_dest_evts _ Hvalid) in Hmid2 as Hxevts.
      apply (mo_same_loc _ Hvalid) in Hmid2 as Hsloc.
      rewrite <-Hsameloc in Hsloc.
      destruct (classic (x = c)) as [H|H].
      { rewrite H in Hmid2.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). auto. }
      apply Hmaxmo in Hxevts; auto.
      pose proof (mo_irr _ Hval) as Hmoirr.
      rewrite <-irreflexive_is_irreflexive in Hmoirr.
      apply (Hmoirr c). destruct_val_exec Hvalid.
      destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
      apply Hmotrans. exists x; auto.
  - destruct Hmid as [[Hmid|Hmid]|Hmid].
    + destruct Hmid as [_ Hmid].
      destruct Hend1 as [[[[Hend1|Hend1]|Hend1]|Hend1]|[[Hend1|Hend1]|Hend1]].
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * destruct Hend1 as [z5 Hend11 Hend12]. rewrite <-cnv_rev in Hend11.
        rew bounded in Hend11. apply simpl_trt_tright in Hend11.
        rewrite Hmid in Hend11. unfold NLE in Hend11. rewrite Hn in Hend11.
        simpl in Hend11. lia.
      * destruct Hend1 as [Hend1 _]. rewrite Hmid in Hend1.
        apply (sb_num_ord _ _ _ Hnumco) in Hend1. rewrite Hn in Hend1. 
        simpl in Hend1. lia.
      * destruct Hend1 as [Hend1 _]. rewrite Hend1 in Hmid.
        rewrite Hmid in Hcwrite. rewrite Hn in Hcwrite. simpl in Hcwrite. destruct Hcwrite.
      * destruct Hend1 as [z5 Hend11 Hend12]. rewrite <-cnv_rev in Hend11.
        destruct Hend11 as [Hend11 _].
        destruct Hmaxmo as [_ Hmaxmo]. rew bounded in Hend12.
        apply simpl_trt_hyp in Hend12 as [_ [Hend12 _]]. rewrite Hend11 in Hend12.
        inversion Hcomp as [Hvalid _].
        apply (mo_dest_evts _ Hvalid) in Hend12 as Hz4evts.
        apply (mo_same_loc _ Hvalid) in Hend12 as Hsloc.
        rewrite <-Hsameloc in Hsloc.
        destruct (classic (z4 = c)) as [H|H].
        { rewrite H in Hend12.
          pose proof (mo_irr _ Hval) as Hmoirr.
          rewrite <-irreflexive_is_irreflexive in Hmoirr.
          apply (Hmoirr c); auto. }
        apply Hmaxmo in Hz4evts; auto.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). destruct_val_exec Hvalid.
        destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
        apply Hmotrans. exists z4; auto.
    + destruct Hmid as [_ Hmid].
      destruct Hend1 as [[[[Hend1|Hend1]|Hend1]|Hend1]|[[Hend1|Hend1]|Hend1]].
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * rewrite Hmid in Hend1. apply simpl_trt_hyp in Hend1 as [Hend1 _].
        unfold NLE in Hend1. rewrite Hn in Hend1. simpl in Hend1. lia.
      * destruct Hend1 as [z5 Hend11 Hend12]. rewrite <-cnv_rev in Hend11.
        rew bounded in Hend11. apply simpl_trt_tright in Hend11.
        rewrite Hmid in Hend11. unfold NLE in Hend11. rewrite Hn in Hend11.
        simpl in Hend11. lia.
      * destruct Hend1 as [Hend1 _]. rewrite Hmid in Hend1.
        apply (sb_num_ord _ _ _ Hnumco) in Hend1. rewrite Hn in Hend1. 
        simpl in Hend1. lia.
      * destruct Hend1 as [Hend1 _]. rewrite Hend1 in Hmid.
        rewrite Hmid in Hcwrite. rewrite Hn in Hcwrite. simpl in Hcwrite. destruct Hcwrite.
      * destruct Hend1 as [z5 Hend11 Hend12]. rewrite <-cnv_rev in Hend11.
        destruct Hend11 as [Hend11 _].
        destruct Hmaxmo as [_ Hmaxmo]. rew bounded in Hend12.
        apply simpl_trt_hyp in Hend12 as [_ [Hend12 _]]. rewrite Hend11 in Hend12.
        inversion Hcomp as [Hvalid _].
        apply (mo_dest_evts _ Hvalid) in Hend12 as Hz4evts.
        apply (mo_same_loc _ Hvalid) in Hend12 as Hsloc.
        rewrite <-Hsameloc in Hsloc.
        destruct (classic (z4 = c)) as [H|H].
        { rewrite H in Hend12.
          pose proof (mo_irr _ Hval) as Hmoirr.
          rewrite <-irreflexive_is_irreflexive in Hmoirr.
          apply (Hmoirr c); auto. }
        apply Hmaxmo in Hz4evts; auto.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). destruct_val_exec Hvalid.
        destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
        apply Hmotrans. exists z4; auto.
    + destruct Hmid as [z5 Hmid1 Hmid2]. rewrite <-cnv_rev in Hmid1.
      destruct Hmid1 as [Hz5c _]. apply simpl_trt_hyp in Hmid2 as [_ [Hmid2 _]].
      destruct Hmaxmo as [_ Hmaxmo]. inversion Hcomp as [Hvalid _].
      rewrite Hz5c in Hmid2.
      apply (mo_dest_evts _ Hvalid) in Hmid2 as Hz1evts.
      apply (mo_same_loc _ Hvalid) in Hmid2 as Hsloc.
      rewrite <-Hsameloc in Hsloc.
      destruct (classic (z1 = c)) as [H|H].
      { rewrite H in Hmid2.
        pose proof (mo_irr _ Hval) as Hmoirr.
        rewrite <-irreflexive_is_irreflexive in Hmoirr.
        apply (Hmoirr c). auto. }
      apply Hmaxmo in Hz1evts; auto.
      pose proof (mo_irr _ Hval) as Hmoirr.
      rewrite <-irreflexive_is_irreflexive in Hmoirr.
      apply (Hmoirr c). destruct_val_exec Hvalid.
      destruct_mo_v Hmo_v. destruct Hmopo as [_ [Hmotrans _]].
      apply Hmotrans. exists z1; auto.
Qed.

(** Changing the value read by the first conflicting event to the value written
by the last write event in the modification order preserves the sequential
consistency of an execution *)

Lemma change_val_sc (ex1 ex2: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  complete_exec ex1 ->
  rc11_consistent ex1 ->
  numbering_coherent ex1 ->
  numbering_injective ex1 ->
  minimal_conflicting_pair ex1 bound j k ->
  numbering k > numbering j ->
  max_mo c ex1 l ->
  change_val_read_k ex1 ex2 k c n l v ->
  sc_consistent ex2.
Proof.
  intros Hcomp Hrc11 Hmcp Hord Hmaxmo Hchval.
  split.
  - eapply change_val_atomicity; eauto.
  - eapply change_val_eco_ac; eauto.
Qed.

Lemma change_val_in_res_sc (ex1 res ex2: Execution) (bound: nat) (j k c n: Event) (l: Loc) (v: Val):
  complete_exec ex1 ->
  rc11_consistent ex1 ->
  numbering_coherent ex1 ->
  numbering_injective ex1 ->
  minimal_conflicting_pair ex1 bound j k ->
  (numbering k) > (numbering j) ->
  sb_closed_restriction ex1 res (sbrf_before_jk ex1 bound j k) ->
  max_mo c res l ->
  change_val_read_k res ex2 k c n l v ->
  sc_consistent ex2.
Proof.
  intros Hcomp Hrc11 Hnumco Hnuminj Hmcp Hord Hres Hmaxmo Hchval.
  assert (prefix res ex1) as Hpre.
  { eapply prefix_res_ex; eauto. }
  eapply (change_val_sc res _ bound j k c n); eauto.
  - eapply prefix_complete; eauto.
  - eapply prefix_rc11_consistent; eauto.
  - eapply numbering_coherent_pre; eauto.
  - eapply mcp_in_res; eauto.
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


Inductive sameP (a b: Execution) : Prop :=
  (*
  | sameP_pre : 
    forall j k bound, minimal_conflicting_pair a bound j k ->
                      sb_closed_restriction a b (sbrf_before_jk b bound j k) -> 
                      sameP a b
  *)
  | sameP_resthenchval : forall j k bound res c n v l,
      sb_closed_restriction res b (sbrf_before_jk b bound j k) ->
      change_val_read_k res a k c n l v -> sameP a b
  | sameP_mo : eq_mod_mo a b -> sameP a b
  | sameP_trans : forall c, sameP a c -> sameP c b -> sameP a b.

Lemma sameP_numbering_coherent (a b: Execution):
  sameP a b ->
  numbering_coherent b ->
  numbering_coherent a.
Proof.
  intros Hsame Hnumco.
  induction Hsame.
  - eapply numbering_coherent_pre; eauto.
  - eapply change_val_numco; eauto.
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
  - eapply change_val_numinj; eauto.
  - eapply eq_mod_mo_numinj; eauto.
  - intuition auto.
Qed.

Lemma sameP_valid (a b: Execution):
  sameP a b ->
  valid_exec b ->
  numbering_coherent b ->
  valid_exec a.
Proof.
  intros Hsame Hval Hnumco.
  induction Hsame as [a b Hpre|a b k c n v l Hchval|a b Hmo|a b c Ht1 IH1 Ht2 IH2].
  - eapply prefix_valid; eauto.
  - eapply change_val_valid; eauto.
  - destruct Hmo as [Hvalmo [Hevts [Hsb [Hrmw Hrf]]]].
    unfold complete_exec, valid_exec in *.
    rewrite Hevts, Hsb, Hrmw, Hrf.
    rewrite Hevts in Hvalmo. intuition auto.
  - apply IH1.
    + apply IH2; auto.
    + eapply sameP_numbering_coherent; eauto.
Qed.

Lemma sameP_complete (a b: Execution):
  sameP a b ->
  complete_exec b ->
  numbering_coherent b ->
  complete_exec a.
Proof.
  intros Hsame Hval Hnumco.
  induction Hsame as [a b Hpre|a b k c n v l Hchval|a b Hmo|a b c Ht1 IH1 Ht2 IH2].
  - eapply prefix_complete; eauto.
  - eapply change_val_complete; eauto.
  - destruct Hmo as [Hvalmo [Hevts [Hsb [Hrmw Hrf]]]].
    unfold complete_exec, valid_exec in *.
    rewrite Hevts, Hsb, Hrmw, Hrf.
    rewrite Hevts in Hvalmo. intuition auto.
  - apply IH1.
    + apply IH2; auto.
    + eapply sameP_numbering_coherent; eauto.
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

Lemma res_chval_not_sbrf (e res fex: Execution) (b l v: nat) (j k c n s: Event):
  rc11_consistent e ->
  minimal_conflicting_pair e b j k ->
  sb_closed_restriction e res (sbrf_before_jk e b j k) ->
  change_val_read_k res fex k c n l v ->
  ~(sb fex ⊔ rf fex) j s.
Proof.
  intros Hrc11 Hmcp Hres Hchval.
  inversion_chval Hchval. rewrite Hsb, Hrf. intros [[Hnot|Hnot]|[Hnot|Hnot]].
  - rew bounded in Hnot.
    destruct Hnot as [z1 [z2 [Heq1 _] Hrel] [Heq2 Hnum2]].
    destruct_res Hres. rewrite Hsb0 in Hrel.
    destruct Hrel as [j2 [j1 Ht1 Hrel] Ht2].
    destruct Ht1 as [Heqt1 _].
    destruct Ht2 as [Heqt2 Ht2].
    rewrite <-Heqt1 in Hrel. unfold sbrf_before_jk in Ht2.
    destruct Ht2 as [Ht2|Ht2].
    + destruct Hrc11 as [_ [_ [_ Hnothinair]]].
      apply (Hnothinair j). rewrite tc_inv_dcmp2.
      exists j2.
      * rewrite Heq1. incl_rel_kat Hrel.
      * rew bounded in Ht2. incl_rel_kat Ht2.
    + admit.
Admitted.
    

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
  pose proof (exec_sc_no_conflict e' (sameP_valid _ _ Hsame (proj1 Hcomp) Hnumco) Hrc11 Hnotsc) as Hexpi.
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
    + (* race_implies_race_change_mo *)
      exists j, k. split.
      * apply race_implies_race_change_mo; eauto.
        eapply race_sym. eapply mcp_write_race; eauto.
        eapply mcp_is_sym; eauto.
      * eapply mcp_at_least_one_not_sc in Hmcp.
        destruct (classic (get_mode j <> Sc));
        destruct (classic (get_mode k <> Sc));
        intuition auto.

  (* If this event is a read *)
  - destruct (sb_res_exists _ _ _ _ (sameP_valid _ _ Hsame Hval Hnumco) Hmcp) as [res Hres].
    assert (is_write j) as Hwj.
    { destruct (mcp_one_is_write _ _ _ _ Hmcp) as [Hk|Hk]. 
        + auto.
        + destruct k; unfold is_write, is_read in Hk, Hkr;
          intuition auto. }
    assert (In _ (writes (evts res)) j) as Hjevts.
    { split; auto. 
      destruct_res Hres. rewrite Hevts. left. apply one_incl_rtc. split; auto.
    }
    destruct (loc_of_write _ Hwj) as [l Hloc].
    edestruct (exists_max_mo res l) as [c Hcmax].
    { exists j; intuition auto. }
    destruct (classic (c = j)) as [Hjc|Hjc].
    + admit.
    + inversion Hcmax as [_ [[_ Hcw] _]].
      destruct (val_of_write _ Hcw) as [v Hv].
      destruct (change_val_read_exists res k c l v) as [fex [n Hfex]]; auto.
      * destruct_res Hres. rewrite Hevts. right. apply one_incl_rtc. split; auto.
      * destruct Hcmax as [_ [[? _] _]]. auto.
      * pose proof (mcp_same_loc _ _ _ _ Hmcp). congruence.
      * destruct Hcmax as [? _]. auto. 
      * { inversion He'comp as [He'val _]. 
          eapply (mcp_all_smaller_snd_evt _ _ _ _ _ He'val He'numco); eauto.
          - destruct Hcmax as [_ [[Hcin _] _]]. destruct_res Hres.
            rewrite Hevts in Hcin.
            eapply sbrf_before_jk_bounded; eauto.
          - intros Heq. rewrite Heq in Hcw. destruct k;
            unfold is_read in Hkr; unfold is_write in Hcw; intuition auto.
        }
      * { exists fex. split;[|split].
          - eapply sameP_trans.
            + eapply sameP_trans.
              * eapply sameP_chval. eauto.
              * eapply sameP_pre. eapply prefix_res_ex; eauto.
            + auto.
          - eapply (change_val_in_res_sc e' res fex); eauto.
          - assert (valid_exec fex) as Hvalfex.
            { eapply sameP_valid.
              - eapply sameP_chval; eauto.
              - eapply sameP_valid.
                + eapply sameP_pre. eapply prefix_res_ex; eauto.
                + destruct He'comp. auto.
                + auto.
              - eapply sameP_numbering_coherent. 
                + eapply sameP_pre. eapply prefix_res_ex; eauto.
                + auto.
            }
            exists j, n. split.
            + split;[|split;[|split;[|split]]].
              * left. auto.
              * inversion_chval Hfex. intros Heq. rewrite Heq, Hn in Hwj.
                unfold is_write in Hwj. inversion Hwj.
              * inversion_chval Hfex. rewrite Hn. simpl. auto.
              * unshelve (eapply (incl_not_rel_thm _ (hb_incl_sbrf _ Hvalfex))).
                eapply not_rel_tc. intros s. inversion_chval Hfex.
                rewrite Hsb, Hrf. intros [[H|H]|[H|H]].
                -- destruct_res Hres.
        }

      
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












