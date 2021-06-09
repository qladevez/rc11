(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.
From RC11 Require Import util proprel_classic.
From RC11 Require Import exec.
Require Import Ensembles Classical_Prop.

Open Scope rel_notations.

(** This file defines what it means to be valid on the RC11 memory model *)

Section RC11.

Variable ex: Execution.

(** ** Release sequence *)

(** The release sequence of a write event contains the write itself (if it is
atomic) and all later atomic writes to the same location in the same thread, as 
well as all read-modify-write that recursively read from such writes. *)

Definition rs  :=
  [W] ⋅ (res_eq_loc (sb ex)) ? ⋅ [W] ⋅ [Mse Rlx] ⋅ ((rf ex) ⋅ (rmw ex)) ^*.

Lemma rfrmw_rtc_same_loc (x y: Event):
  valid_exec ex ->
  (rf ex⋅rmw ex)^* x y ->
  get_loc x = get_loc y.
Proof.
  intros Hval. generalize x y. eapply rtc_ind.
  - intros z1 z2 [z3 Hrf Hrmw].
    apply (rf_same_loc _ Hval) in Hrf.
    apply (rmw_same_loc _ Hval) in Hrmw.
    congruence.
  - intuition auto.
  - intuition congruence.
Qed.

Lemma rfrmw_rtc_rf_same_loc (x y: Event):
  valid_exec ex ->
  ((rf ex⋅rmw ex)^*⋅(rf ex)) x y ->
  get_loc x = get_loc y.
Proof.
  intros Hval [z Hrel Hrf].
  apply (rfrmw_rtc_same_loc _ _ Hval) in Hrel.
  apply (rf_same_loc _ Hval) in Hrf.
  congruence.
Qed.

Lemma rs_same_loc (x y: Event):
  valid_exec ex ->
  rs x y ->
  get_loc x = get_loc y.
Proof.
  intros Hval Hrs.
  destruct Hrs as [z Hsbloc Hrfrmw].
  destruct Hsbloc as [z2 Hsbloc [Heq1 _]]; rewrite Heq1 in Hsbloc.
  destruct Hsbloc as [z3 Hsbloc [Heq2 _]]; rewrite Heq2 in Hsbloc.
  destruct Hsbloc as [z4 [Heq3 _] Hsbloc]; rewrite <-Heq3 in Hsbloc.
  destruct Hsbloc as [[_ Heq4]|Heq4];
  apply (rfrmw_rtc_same_loc _ _ Hval) in Hrfrmw; congruence.
Qed.

Lemma rsrf_same_loc (x y: Event):
  valid_exec ex ->
  (rs⋅rf ex) x y ->
  get_loc x = get_loc y.
Proof.
  intros Hval [z Hrs Hrf].
  apply (rs_same_loc _ _ Hval) in Hrs.
  apply (rf_same_loc _ Hval) in Hrf.
  congruence.
Qed.

(** ** Synchronises with *)

(** A release event [a] synchronises with an acquire event [b] whenever [b] (or,
in case [b] is a fence, a [sb]-prior read) reads from the release sequence of
[a] *)

Definition sw :=
  [Mse Rel] ⋅ ([F] ⋅ (sb ex)) ? ⋅ rs ⋅ (rf ex) ⋅ [R] ⋅ [Mse Rlx] ⋅ ((sb ex) ⋅ [F]) ? ⋅ [Mse Acq].

(** The synchronises-with relation is included in the transitive closure of the
union of sequenced-before and reads-from *)

Lemma sw_incl_sbrf:
  valid_exec ex ->
  sw ≦ ((sb ex) ⊔ (rf ex))^+.
Proof.
  intros Hval.
  unfold sw, rs. rewrite rmw_incl_sb.
  rewrite res_eq_loc_incl_itself. kat. auto using Hval.
Qed.
  
(** ** Happens-before *)

(** Intuitively, the happens-before relation records when an event is globally
perceived as occurring before another one.
We say that an event happens-before another one if there is a path between the
two events consisting of [sb] and [sw] edges *)

Definition hb  :=
  ((sb ex) ⊔ sw)^+.

(** The happens-before relation is included in the transitive closure of the
union of sequenced-before and reads-from *)

Lemma hb_incl_sbrf:
  valid_exec ex ->
  hb ≦ ((sb ex) ⊔ (rf ex))^+.
Proof.
  intros Hval.
  unfold hb. rewrite (sw_incl_sbrf Hval). kat.
Qed.

(** sequenced-before is included in happens-before *)

Lemma sb_incl_hb:
  sb ex ≦ hb.
Proof.
  unfold hb. kat.
Qed.

(** ** SC-before *)

Definition scb :=
 (sb ex) ⊔  ((res_neq_loc (sb ex)) ⋅ hb ⋅ (res_neq_loc (sb ex))) ⊔ (res_eq_loc hb) ⊔ (mo ex) ⊔  (rb ex).

(** happens-before can be decomposed in a subset of happens-before included in
SC-before, and the rest of happens-before *)

Lemma hb_dcmp:
  valid_exec ex ->
  hb = ((sb ex) ⊔  ((res_neq_loc (sb ex)) ⋅ hb ⋅ (res_neq_loc (sb ex))) ⊔ (res_eq_loc hb)) ⊔
       ((res_eq_loc (sb ex) ⋅ hb) ⊔
        (hb ⋅ res_eq_loc (sb ex)) ⊔
        (sw ⋅ hb) ⊔
        (hb ⋅ sw) ⊔
        sw).
Proof.
  intros Hval. apply ext_rel, antisym.
  - intros x y Hrel.
    unfold hb in Hrel. rewrite tc_inv_dcmp2 in Hrel.
    destruct Hrel as [z Hxz Hhb].
    rewrite rtc_inv_dcmp6 in Hhb.
    destruct Hhb as [Hzy|Hhb].
    { simpl in Hzy. rewrite Hzy in Hxz. destruct Hxz as [Hxz|Hxz].
      - left; left; left. auto.
      - right; right. auto.
    }
    rewrite tc_inv_dcmp in Hhb. destruct Hhb as [w Hhb Hwy].
    rewrite rtc_inv_dcmp6 in Hhb. destruct Hhb as [Hzw|Hzw].
    + simpl in Hzw. rewrite <-Hzw in Hwy.
      destruct Hxz as [Hxz|Hxz]; destruct Hwy as [Hwy|Hwy].
      * left; left; left. apply (sb_trans _ Hval). exists z; auto.
      * right; left; right. exists z; auto.
        unfold hb. incl_rel_kat Hxz.
      * right; left; left; right. exists z; auto.
        unfold hb. incl_rel_kat Hwy.
      * right; left; right. exists z; auto.
        unfold hb. incl_rel_kat Hxz.
    + destruct Hxz as [Hxz|Hxz]; destruct Hwy as [Hwy|Hwy].
      * destruct (classic (get_loc x = get_loc z)) as [Heqxz|Hneqxz].
        { right; left; left; left; left. exists z.
          - split; auto.
          - unfold hb. rewrite tc_inv_dcmp. exists w.
            + incl_rel_kat Hzw.
            + incl_rel_kat Hwy.
        }
        destruct (classic (get_loc w = get_loc y)).
        { right; left; left; left; right. exists w.
          - unfold hb. rewrite tc_inv_dcmp2. exists z.
            + incl_rel_kat Hxz.
            + incl_rel_kat Hzw.
          - split; auto.
        } 
        left; left; right.
        { exists w. exists z.
          - split; auto.
          - unfold hb. auto.
          - split; auto.
        }
      * right; left; right.
        exists w; auto.
        unfold hb. rewrite tc_inv_dcmp2. exists z.
        -- incl_rel_kat Hxz.
        -- incl_rel_kat Hzw.
      * right; left; left; right.
        exists z; auto.
        unfold hb. rewrite tc_inv_dcmp. exists w.
        -- incl_rel_kat Hzw.
        -- incl_rel_kat Hwy.
      * right; left; left; right.
        exists z; auto.
        unfold hb. rewrite tc_inv_dcmp. exists w.
        -- incl_rel_kat Hzw.
        -- incl_rel_kat Hwy.
  - unfold hb. intros x y [[[Hrel|Hrel]|Hrel]|
                           [[[[Hrel|Hrel]|Hrel]|Hrel]|Hrel]];
    try (incl_rel_kat Hrel).
    + destruct Hrel as [z [w [Hr1 _] Hr2] [Hr3 _]].
      rewrite tc_inv_dcmp2. exists w.
      { incl_rel_kat Hr1. }
      rewrite rtc_inv_dcmp6. right.
      rewrite tc_inv_dcmp. exists z.
      * incl_rel_kat Hr2.
      * incl_rel_kat Hr3.
    + destruct Hrel as [Hrel _]. auto.
    + destruct Hrel as [z [Hr1 _] Hr2].
      rewrite tc_inv_dcmp2. exists z.
      * incl_rel_kat Hr1.
      * incl_rel_kat Hr2.
    + destruct Hrel as [z Hr1 [Hr2 _]].
      rewrite tc_inv_dcmp. exists z.
      * incl_rel_kat Hr1.
      * incl_rel_kat Hr2.
Qed.

(** ** Partial-SC base *)

(** We give a semantic to SC atomics by enforcing the order in which they should
occur *)

Definition psc_base :=
  ([M Sc] ⊔ (([F] ⋅ [M Sc]) ⋅ (hb ?))) ⋅
  (scb) ⋅
  ([M Sc] ⊔ ((hb ?) ⋅ ([F] ⋅ [M Sc]))).

(** ** Partial-SC fence *)

(** We give a semantic to SC fences by enforcing the order in which they should
occur *)

Definition psc_fence :=
  [F] ⋅ [M Sc] ⋅ (hb ⊔ (hb ⋅ (eco ex) ⋅ hb)) ⋅ [F] ⋅ [M Sc].

(** ** Partial SC *)

Definition psc :=
  psc_base ⊔ psc_fence.

(** * RC11-consistency *)

(** ** Coherence *)

(** The coherence condition is also called SC-per-location. It guarantees that,
if we consider only the events on one location in the execution, the subset of
the execution is sequentially consistent. In practice, it forbids a set of 
patterns in executions. These patterns are detailed in proposition 1 of section
3.4 in the article, and we prove that they are indeed forbidden by the coherence
condition *)

Definition coherence :=
  forall x, ~(hb ⋅ (eco ex) ?) x x.
  

(** In a coherent execution, [hb] is irreflexive. This means that an event
should not occur before itself. *)

Lemma coherence_irr_hb:
  coherence -> (forall x, ~hb x x).
Proof.
  intros H x Hnot.
  apply (H x). exists x.
  - auto.
  - right. simpl; auto.
Qed.

(** In a coherent execution, [rf];[hb] is irreflexive. This means that an event
should not read a value written by a write event occuring in the future. *)

Lemma coherence_no_future_read:
  coherence -> (forall x, ~ ((rf ex) ⋅ hb) x x).
Proof.
  intros H x Hnot.
  destruct Hnot.
  eapply H. exists x.
  - eauto.
  - left. apply tc_incl_itself. left. left. auto.
Qed.

(** In a coherent execution, [mo];[rf];[hb] is irreflexive. This means that a
write [w1] can not occur in modification order before a write [w2], if the value
written by [w2] was read by a read event sequenced before [w1]. It forbids the
following pattern in executions:

<<
     rf
 Wx----->Rx
 ^        |
 |        |sb
 |        v
 +------+Wx
     mo
>>
*)

Lemma coherence_coherence_rw:
  coherence -> (forall x, ~ ((mo ex) ⋅ (rf ex) ⋅ hb) x x).
Proof.
  intros H x Hnot.
  destruct Hnot as [z [z' Hmo Hrf] Hhb].
  apply (H z). exists x.
  - auto.
  - left. apply tc_trans with (y := z'); apply tc_incl_itself.
    + left. right. auto.
    + left. left. auto.
Qed.

(** In a coherent execution, [mo];[hb] is irreflexive. This means that a write
can not modify the memory before a write that precedes it in sequenced-before *)

Lemma coherence_coherence_ww:
  coherence -> (forall x, ~ ((mo ex) ⋅ hb) x x).
Proof.
  intros H x Hnot.
  destruct Hnot as [z Hmo Hhb].
  apply (H z). exists x.
  - auto.
  - left. apply tc_incl_itself. left. right. auto.
Qed.

(** In a coherent execution, [mo];[hb];[rf-1] is irreflexive. This means that
a read event cannot read from a write event whose value has been overwritten
by another write, preceding the read in sequenced before. It forbids the
following pattern in executions:

<<
      mo
  Wx----->Wx
  |        |
  |        | sb
  |        v
  +------>Rx
      rf
>>
*)

Lemma coherence_coherence_wr:
  coherence -> (forall x, ~ ((mo ex) ⋅ hb ⋅ (rf ex)°) x x).
Proof.
  intros H x Hnot.
  destruct Hnot as [z [y Hmo Hhb] Hinvrf].
  apply (H y). exists z.
  - auto.
  - left. apply tc_incl_itself.
    right.
    exists x; auto.
Qed.

(** In a coherent execution, [mo];[rf];[hb];[rf-1] is irreflexive. This means
that if two reads following each other in sequenced-before read values written
by two write events, these two write events must appear in the same order in the
modification order. We forbid the following pattern in executions:

<<
        rf
   Wx-------->Rx
   ^           |
 mo|           |sb
   |           v
   Wx+------->Rx
        rf
>>
*)

Lemma coherence_coherence_rr:
  coherence -> (forall x, ~ ((mo ex) ⋅ (rf ex) ⋅ hb ⋅ (rf ex)°) x x).
Proof.
  intros H x Hnot.
  destruct Hnot as [w [y' [z Hmo Hrf] Hhb] Hinvr].
  apply (H y'). exists w.
  - auto.
  - left. apply tc_trans with (y := z); apply tc_incl_itself.
    + right. exists x; auto.
    + left. left. auto.
Qed.

(** The coherence condition is equivalent to the uniproc condition in some other
memory models *)

Theorem coherence_is_uniproc:
  valid_exec ex -> coherence -> irreflexive ((sb ex) ⋅ (eco ex)).
Proof.
  intros Hval Hco.
  apply seq_refl_incl_left with (r3 := hb).
  - unfold sb, hb. kat.
  - rewrite (eco_rfmorb_seq_rfref _ Hval).
    unfold irreflexive.
    ra_normalise.
    repeat (rewrite union_inter).
    repeat (apply leq_cupx).
    + pose proof (coherence_no_future_read Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      apply refl_shift in H. auto.
    + pose proof (coherence_coherence_wr Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      apply refl_shift in H. rewrite dotA in H. apply refl_shift in H.
      fold rb in H. auto.
    + pose proof (coherence_coherence_ww Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      apply refl_shift in H. auto.
    + pose proof (coherence_coherence_rr Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      do 2 (apply refl_shift in H; repeat (rewrite dotA in H)).
      unfold rb. repeat (rewrite dotA). auto.
    + pose proof (coherence_coherence_rw Hco).
      rewrite irreflexive_is_irreflexive in H. unfold irreflexive in H.
      apply refl_shift in H. rewrite dotA in H. auto.
Qed.

(** ** Atomicity *)

(** Atomicity ensures that the read and the write composing a RMW pair are
adjacent in [eco]: there is no write event in between *)

Definition atomicity :=
  forall x y, ~ ((rmw ex) ⊓ ((rb ex) ⋅ (mo ex))) x y.

(** ** SC *)

(** The SC condition gives a semantic to SC atomics and fences in executions. It
is defined. It is defined  *)

Definition SC :=
  acyclic psc.

(** ** No-thin-air *)

(** We want to forbid out-of-thin-air, which means excluding executions where
the value written by a write event depends on the value read by a read event,
which reads from this same write event. *)

Definition no_thin_air :=
  acyclic ((sb ex) ⊔ (rf ex)).

(** ** RC11-consistent executions *)

(** An execution is RC11-consistent when it verifies the four conditions we just
defined *)

Definition rc11_consistent :=
  coherence /\ atomicity /\ SC /\ no_thin_air.

(** Coherence implies that [rf;rmw] is included in [mo] *)

Lemma coherence_rfrmw_incl_mo:
  valid_exec ex ->
  rc11_consistent ->
  (rf ex⋅rmw ex) ≦ mo ex.
Proof.
  intros Hval Hrc11 x y [z Hrf Hrmw].
  apply (rf_orig_write _ Hval) in Hrf as Hxw.
  apply (rmw_dest_write _ Hval) in Hrmw as Hyw.
  apply (rf_same_loc _ Hval) in Hrf as Hxzloc.
  apply (rmw_same_loc _ Hval) in Hrmw as Hzyloc.
  assert (x <> y).
  { intros Heq. rewrite Heq in Hrf.
    apply (rmw_incl_sb _ Hval) in Hrmw.
    destruct Hrc11 as [_ [_ [_ Hnoota]]]. eapply Hnoota.
    eapply tc_trans; [incl_rel_kat Hrf|incl_rel_kat Hrmw]. }
  destruct (loc_of_write _ Hxw) as [l Heqloc].
  inverse_val_exec Hval. destruct_mo_v Hmo_v.
  edestruct (Hmotot l x y) as [[Hmo _]|[Hmo _]].
  - auto.
  - repeat (apply conj); auto.
    eapply rf_orig_evts; eauto.
  - repeat (apply conj); auto.
    + eapply rmw_dest_evts; eauto.
    + congruence.
  - auto.
  - apply (rmw_incl_sb _ Hval) in Hrmw.
    destruct Hrc11 as [Hco _]. exfalso. apply (Hco z).
    exists y. 
    + unfold hb. incl_rel_kat Hrmw.
    + left. eapply tc_trans.
      * incl_rel_kat Hmo.
      * incl_rel_kat Hrf.
Qed.

(** Coherence implies that [rmw] is included in [rb] *)

Lemma rc11_rmw_incl_rb:
  complete_exec ex ->
  rc11_consistent ->
  rmw ex ≦ (rb ex).
Proof.
  intros Hcomp [Hco _] x y Hrmw.
  inversion Hcomp as [Hval _].
  unfold coherence in Hco.
  unfold hb, eco in Hco.
  unfold rb. byabsurd.
  destruct (Hco x).
  assert (exists z, (rf ex) z x) as [z Hrf].
  { destruct Hcomp as [_ Hrf].
    unfold ran in Hrf. apply Hrf.
    split.
    - apply (rmw_orig_evts _ Hval _ y Hrmw).
    - apply (rmw_orig_read _ Hval _ y Hrmw).
  }
  destruct (classic (y = z)) as [Hyz|Hyz].
  - apply (rmw_incl_sb _ Hval) in Hrmw.
    rewrite <-Hyz in Hrf.
    exists y.
    + apply tc_incl_itself. left. auto.
    + left. apply tc_incl_itself. left. left. auto.
  - assert (exists l, (get_loc y = Some l) /\ (get_loc z = Some l))
    as [l [Hl1 Hl2]].
    { apply (rf_dest_read _ Hval) in Hrf as Hxw.
      apply (rf_same_loc _ Hval) in Hrf.
      apply (rmw_same_loc _ Hval) in Hrmw.
      rewrite <-Hrmw, Hrf. destruct x.
      - exists l. intuition auto.
      - exists l. intuition auto.
      - simpl in Hxw. intuition auto.
    }
    edestruct (mo_diff_write _ Hval) as [Hmo|Hmo]; eauto.
    + repeat (apply conj).
      * apply (rmw_dest_evts _ Hval x). auto.
      * apply (rmw_dest_write _ Hval x). auto.
      * eauto.
    + repeat (apply conj).
      * apply (rf_orig_evts _ Hval _ x). auto.
      * apply (rf_orig_write _ Hval _ x). auto.
      * auto.
    + exists y.
      { apply (rmw_incl_sb _ Hval) in Hrmw.
        apply (incl_rel_thm Hrmw). kat. }
      left. apply tc_trans with z.
      * apply (incl_rel_thm Hmo). kat.
      * apply (incl_rel_thm Hrf). kat.
    + destruct Hcontr. exists z.
      * apply (incl_rel_thm Hrf). kat.
      * apply (incl_rel_thm Hmo). kat.
Qed.

Lemma rfrmw_rtc_rf_diff (x y: Event):
  valid_exec ex ->
  rc11_consistent ->
  ((rf ex⋅rmw ex)^*⋅rf ex) x y ->
  x <> y.
Proof.
  intros Hval Hrc11 Hrel Heq.
  destruct Hrc11 as [_ [_ [_ Hnoota]]].
  rewrite <-Heq in Hrel.
  eapply Hnoota. apply (incl_rel_thm Hrel).
  rewrite (rmw_incl_imm_sb _ Hval).
  rewrite imm_rel_incl_rel.
  kat.
Qed.

Lemma rsrf_diff (x y: Event):
  valid_exec ex ->
  rc11_consistent ->
  (rs⋅rf ex) x y ->
  x <> y.
Proof.
  intros Hval Hrc11 Hrsrf Heq.
  destruct Hrc11 as [_ [_ [_ Hnoota]]].
  rewrite <-Heq in Hrsrf.
  eapply Hnoota. apply (incl_rel_thm Hrsrf).
  unfold rs.
  rewrite res_eq_loc_incl_itself.
  rewrite (rmw_incl_imm_sb _ Hval).
  rewrite imm_rel_incl_rel.
  kat.
Qed.

Lemma rsrf_left_write (x y: Event):
  (rs⋅rf ex) x y ->
  is_write x.
Proof.
  intros Hrel.
  unfold rs in Hrel.
  repeat (rewrite seq_assoc in Hrel).
  destruct Hrel as [_ [_ Hw] _]. auto.
Qed.

Lemma rfrmw_rtc_rf_left_write (x y: Event):
  valid_exec ex ->
  ((rf ex⋅rmw ex)^*⋅rf ex) x y ->
  is_write x.
Proof.
  intros Hval [z Hrel Hrf].
  rewrite rtc_inv_dcmp6 in Hrel. destruct Hrel as [Hrel|Hrel].
  - simpl in Hrel. rewrite <-Hrel in Hrf.
    eapply rf_orig_write; eauto.
  - rewrite tc_inv_dcmp2 in Hrel. destruct Hrel as [z2 Hrel _].
    destruct Hrel as [? Hrf2 _].
    eapply rf_orig_write; eauto.
Qed.

(** * SC-consistent executions *)

(** An execution is SC-consistent if:

- The execution respects the atomicity condition
- The communication relation [eco] is compatible with the program order.
*)

Definition sc_consistent :=
  atomicity /\ acyclic ((sb ex) ⊔ (rf ex) ⊔ (mo ex) ⊔ (rb ex)).

Lemma sc_is_rc11:
  valid_exec ex ->
  sc_consistent ->
  rc11_consistent.
Proof.
  intros Hval [Hato Hsc]. split;[|split;[|split]].
  - intros x Hcyc. apply (Hsc x).
    eapply (incl_rel_thm Hcyc).
    unfold hb, eco, sw, rs.
    rewrite (rmw_incl_sb _ Hval).
    rewrite res_eq_loc_incl_itself. kat.
  - auto.
  - intros x Hcyc. apply (Hsc x).
    eapply (incl_rel_thm Hcyc).
    eapply tc_incl_2. unfold psc. eapply union_incl.
    + unfold psc_base, scb, res_eq_loc, res_neq_loc.
      rewrite leq_cap_l. rewrite leq_cap_l.
      unfold hb, eco, sw, rs.
      rewrite (rmw_incl_sb _ Hval).
      rewrite res_eq_loc_incl_itself. kat.
    + unfold psc_fence, hb, sw, rs, eco.
      rewrite (rmw_incl_sb _ Hval).
      rewrite res_eq_loc_incl_itself. kat.
  - intros x Hcyc. apply (Hsc x).
    eapply (incl_rel_thm Hcyc).
    kat.
Qed.

Lemma rc11_is_sc_rf_incl_hbloc:
  valid_exec ex ->
  (forall e, In _ (evts ex) e -> (get_mode e = Sc)) ->
  rf ex ≦ res_eq_loc hb.
Proof.
  intros Hval Hallsc x y.
  split;[|auto using (rf_same_loc _ Hval)].
  apply tc_incl_itself. right.
  apply (rf_orig_evts _ Hval) in H as Hxevts.
  apply (rf_dest_evts _ Hval) in H as Hyevts.
  apply Hallsc in Hxevts. apply Hallsc in Hyevts.
  exists y. exists y. exists y. exists y.
  exists x. exists x. exists x.
  + split; auto. 
    destruct x; destruct m; compute in Hxevts;
    compute; intuition auto; congruence.
  + right. simpl; auto.
  + exists x. exists x. exists x. exists x.
    * split; auto. eapply rf_orig_write; eauto.
    * right. simpl. auto.
    * split; auto. eapply rf_orig_write; eauto.
    * split; auto. destruct x; destruct m; compute in Hxevts;
      compute; intuition auto; congruence.
    * rewrite rtc_inv_dcmp6. left. simpl. auto.
  + auto.
  + split; auto. eapply rf_dest_read; eauto.
  + destruct y; destruct m; compute in Hyevts;
    compute; intuition auto; congruence.
  + right. simpl; auto.
  + destruct y; destruct m; compute in Hyevts;
    compute; intuition auto; congruence.
Qed.

Lemma rc11_is_sc_aux:
  valid_exec ex ->
  (forall e, In _ (evts ex) e -> (get_mode e = Sc)) ->
  (sb ex ⊔ (eco ex)) ≦ (hb ? ⋅ scb ⋅ hb ?)^+.
Proof.
  intros Hval Hallsc.
  apply union_incl.
  { unfold scb. kat. }
  eapply tc_incl_2.
  apply union_incl;[apply union_incl|].
  - intros x y H. apply tc_incl_itself.
    exists y; [|right;simpl;auto].
    exists x; [right;simpl;auto|].
    left; left; right. eapply rc11_is_sc_rf_incl_hbloc; eauto.
  - unfold scb. kat.
  - unfold scb. kat.
Qed.

Lemma rc11_is_sc:
  valid_exec ex ->
  (forall e, In _ (evts ex) e -> (get_mode e = Sc)) ->
  rc11_consistent ->
  sc_consistent.
Proof.
  intros Hval Hallsc [_ [Hato [Hpsc _]]].
  split. auto.
  intros x Hcyc. apply (Hpsc x).
  eapply (incl_rel_thm Hcyc).
  eapply tc_incl. eapply incl_union_left.
  intros y z Hrel. exists z. exists y.
  - left. split; auto. unfold M. eapply Hallsc.
    eapply sbrfmorb_in_l; eauto.
  - destruct Hrel as [[[Hrel|Hrel]|Hrel]|Hrel]; eapply (incl_rel_thm Hrel).
    + unfold scb. kat.
    + erewrite rc11_is_sc_rf_incl_hbloc; eauto.
      unfold scb. kat.
    + unfold scb. kat.
    + unfold scb. kat.
  - left. split; auto. unfold M. eapply Hallsc.
    eapply sbrfmorb_in_r; eauto.
Qed.

(** If the modification order of a valid execution is empty (meaning there is
one or zero write), the execution is SC-consistent *)

Lemma empty_mo_atomicity:
  valid_exec ex ->
  (mo ex) = empty ->
  atomicity.
Proof.
  intros Hval Hmoempty.
  intros x y [_ [z _ H]].
  rewrite Hmoempty in H.
  destruct H.
Qed.

Lemma empty_mo_ac_eco:
  valid_exec ex ->
  no_thin_air ->
  (mo ex) = empty ->
  acyclic ((sb ex) ⊔ (rf ex) ⊔ (mo ex) ⊔ (rb ex)).
Proof.
  intros Hval Hnoota Hmoempty x Hcyc.
  unfold rb in Hcyc. rewrite Hmoempty in Hcyc.
  apply (Hnoota x). incl_rel_kat Hcyc.
Qed.

Lemma empty_mo_sc_consistent:
  valid_exec ex ->
  no_thin_air ->
  (mo ex) = empty ->
  sc_consistent.
Proof.
  intros Hval Hnoota Hmoempty.
  split.
  - eapply empty_mo_atomicity; eauto.
  - eapply empty_mo_ac_eco; eauto.
Qed.

Lemma not_sc_not_empty_mo:
  valid_exec ex ->
  no_thin_air ->
  ~sc_consistent ->
  (mo ex) <> empty.
Proof.
  intuition auto using empty_mo_sc_consistent.
Qed.

End RC11.
