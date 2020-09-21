(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.
Require Import Ensembles.
Require Import Lia.
Require Import Classical_Prop.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import proprel_classic.
From RC11 Require Import prefix.
From RC11 Require Import rc11.
From RC11 Require Import conflict.

(** This file defines the notion of numbering on the events of an execution. *)

(** ** Definition *)

(** A valid numbering on an execution assigns to each event of the execution a
distinct number such that, if two events are related by the transitive closure
of the union of the sequenced-before and read-from relations of the execution,
then the numbering of the first event is smaller than the numbering of the
second event *)

Definition numbering event : nat :=
  match event with
  | Read eid _ _ _ => eid
  | Write eid _ _ _ => eid
  | Fence eid _ => eid
  end.

(** Two different events can't have the same numbering *)

Definition numbering_injective (ex: Execution) := forall x y,
  x <> y <-> numbering x <> numbering y.

(** Two identical events have the same numbering *)

Lemma numbering_injective_eq (ex: Execution) (x y: Event):
  numbering_injective ex ->
  x = y <-> numbering x = numbering y.
Proof.
  intros Hinj.
  split; intros H.
  - rewrite H; auto.
  - destruct (classic (x = y)) as [Hxy | Hxy].
    + auto.
    + rewrite (Hinj _ _) in Hxy.
      destruct (Hxy H).
Qed.

(** If an event is equal to a read whose numbering is the numbering of a second
event, the two events are equal *)

Lemma eq_num_read {ex: Execution} {x y: Event} {m: Mode} {l: Loc} {v: Val}:
  numbering_injective ex ->
  Read (numbering y) m l v = x ->
  x = y.
Proof.
  intros Hnuminj Heq.
  eapply numbering_injective_eq. eauto.
  rewrite <-Heq. auto.
Qed.

Lemma eq_num_read2 {ex: Execution} {x y: Event} {m: Mode} {l: Loc} {v: Val}:
  numbering_injective ex ->
  x = Read (numbering y) m l v ->
  x = y.
Proof.
  intros Hnuminj Heq.
  eapply numbering_injective_eq. eauto.
  rewrite Heq. auto.
Qed.

(** If a numbering of the events of an execution is injective, the numbering of
the events of its prefixes is also injective *)

Lemma numbering_injective_pre (ex pre: Execution):
  numbering_injective ex ->
  prefix pre ex ->
  numbering_injective pre.
Proof.
  intros Hnuminj Hpre. destruct_prefix Hpre.
  intros x y. apply Hnuminj; apply Hevts; auto.
Qed.

(** If an first event is related to a second event by the union of the sequenced
before relation and reads-from relation, the numbering of the first event is
strictly inferior to the numbering of the second event *)

Definition numbering_coherent ex :=
  forall x y, ((sb ex) ⊔ (rf ex)) x y ->
              numbering x < numbering y.

(** If a first event is related to a second event by the reflexive transitive
closure of the union of the sequenced-before relation and reads-from relation,
the numbering of the second event is greater or equal to the numbering of the
first event *)

Lemma numbering_coherent_rtc (ex: Execution) (x y: Event):
  numbering_coherent ex ->
  ((sb ex) ⊔ (rf ex))^* x y ->
  numbering y >= numbering x.
Proof.
  intros Hnumco.
  generalize dependent y.
  generalize dependent x.
  apply rtc_ind.
  - intros z1 z2 Hstep.
    apply Hnumco in Hstep. lia.
  - intuition auto.
  - intros z1 z2 z3 _ IH1 _ IH2.
    lia.
Qed.

(** If a first event is related to a second event by the transitive closure of 
the union of the sequenced-before relation and reads-from relation, the
numbering of the second event is greater than the numbering of the first
event *)

Lemma numbering_coherent_tc (ex: Execution) (x y: Event):
  numbering_coherent ex ->
  ((sb ex) ⊔ (rf ex))^+ x y ->
  numbering y > numbering x.
Proof.
  intros Hnumco [z Hstep Hrtc].
  apply Hnumco in Hstep.
  apply (numbering_coherent_rtc _ _ _ Hnumco) in Hrtc.
  lia.
Qed.

(** If a first event is related by the sequenced-before relation to a second
event, the numbering of the second event is strictly greater than the numbering
of the first event *)

Lemma sb_num_ord (ex: Execution) (x y: Event):
  numbering_coherent ex ->
  sb ex x y ->
  (numbering y) > (numbering x).
Proof.
  intros Hnumco Hsb.
  eapply numbering_coherent_tc, tc_incl_itself. eauto.
  left; auto.
Qed.

(** If a first event is related by the read-modify-write relation to a second
event, the numbering of the second event is strictly greater than the numbering
of the first event *)

Lemma rmw_num_ord (ex: Execution) (x y: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  rmw ex x y ->
  (numbering y) > (numbering x).
Proof.
  intros Hval Hnumco Hrmw.
  eapply (rmw_incl_sb _ Hval) in Hrmw.
  eapply sb_num_ord; eauto.
Qed.

(** If a first event is related by the reads-from relation to a second event, 
the numbering of the second event is strictly greater than the numbering of the
first event *)

Lemma rf_num_ord (ex: Execution) (x y: Event):
  numbering_coherent ex ->
  rf ex x y ->
  (numbering y) > (numbering x).
Proof.
  intros Hnumco Hsb.
  eapply numbering_coherent_tc, tc_incl_itself; eauto.
  right; auto.
Qed.

(** If the numbering of the events of an execution is coherent, the numbering of
the events of its prefixes is also coherent *)

Lemma numbering_coherent_pre (ex pre: Execution):
  numbering_coherent ex ->
  prefix pre ex ->
  numbering_coherent pre.
Proof.
  intros Hnumco Hpre. destruct_prefix Hpre.
  intros x y Hsbrf.
  apply Hnumco.
  apply (incl_rel_thm Hsbrf). rewrite Hsb, Hrf. kat.
Qed.

(** In every execution, there is a last event whose numbering is greater than
the one of all the other events *)

Axiom numbering_bounded:
  exists e, forall e', numbering e >= numbering e'.
      

(** Tests if the numbering of an event is Less or Equal to a bound *)

Definition NLE (b: nat) : prop_set Event :=
  fun e => b >= (numbering e).

(** Being in the set of events whose numbering is less or equal to a bound is
equivalent to satisfying the NLE test with this bound *)

Lemma NLE_I_evts (bound: nat):
  [I (fun x => bound >= numbering x)] = [NLE bound].
Proof. unfold NLE. kat_eq. Qed.

(** If an event's numbering is less or equal to a bound minus one, it is less
or equal to the bound *)

Lemma NLE_bound_min_one (bound: nat):
  [NLE (bound-1)] ≦ [NLE bound].
Proof.
  intros x y [H1 H2].
  split; auto.
  unfold NLE in *. lia.
Qed.

(** If we test that an event's numbering is less or equal to two bounds, one of
which is strictly inferior to the other, we can replace these two tests by the
test of the event's numbering being less or equal to the smaller bound *)

Lemma nle_double (k1 k2: nat):
  k1 < k2 ->
  [NLE k1]⋅[NLE k2] = [NLE k1].
Proof.
  intros Hord. apply ext_rel, antisym.
  - intros x y [z [Heq1 Hr1] [Heq2 Hr2]].
    rewrite Heq2 in Heq1, Hr2. split; auto.
  - intros x y [Heq Hr].
    exists x; split; auto.
    unfold NLE in Hr. unfold NLE. lia.
Qed.

(** An bounded execution is a restriction of the events and relations of an
execution to the events whose numbering is less or equal to a given bound. *)

Definition bounded_exec (ex: Execution) (n: nat) : Execution :=
  {|
    exec.evts := Intersection _ (evts ex) (fun x => n >= numbering x);
    exec.sb := [NLE n] ⋅ (sb ex) ⋅ [NLE n];
    exec.rmw := [NLE n] ⋅ (rmw ex) ⋅ [NLE n];
    exec.rf := [NLE n] ⋅ (rf ex) ⋅ [NLE n];
    exec.mo := [NLE n] ⋅  (mo ex) ⋅ [NLE n];
  |}.

(** Simplifications of the different getters applied over bounded executions *)

Lemma simpl_evts_be (ex: Execution) (n:nat):
  evts (bounded_exec ex n) = Intersection _ (evts ex) (fun x => n >= numbering x).
Proof. compute; auto. Qed.

Lemma simpl_sb_be (ex: Execution) (n:nat):
  sb (bounded_exec ex n) = [NLE n] ⋅ (sb ex) ⋅ [NLE n].
Proof. compute; auto. Qed.

Lemma simpl_rmw_be (ex: Execution) (n:nat):
  rmw (bounded_exec ex n) = [NLE n] ⋅ (rmw ex) ⋅ [NLE n].
Proof. compute; auto. Qed.

Lemma simpl_rf_be (ex: Execution) (n:nat):
  rf (bounded_exec ex n) = [NLE n] ⋅ (rf ex) ⋅ [NLE n].
Proof. compute; auto. Qed.

Lemma simpl_mo_be (ex: Execution) (n:nat):
  mo (bounded_exec ex n) = [NLE n] ⋅ (mo ex) ⋅ [NLE n].
Proof. compute; auto. Qed.

Lemma simpl_rb_be (ex: Execution) (n:nat):
  rb (bounded_exec ex n) ≦ [NLE n] ⋅ (rb ex) ⋅ [NLE n].
Proof. 
  unfold rb. rewrite simpl_mo_be, simpl_rf_be.
  rewrite 2dot_cnv, injcnv.
  kat.
Qed.

Create HintDb bounded_exec_db.

Hint Rewrite simpl_sb_be simpl_rmw_be simpl_rf_be simpl_mo_be : bounded_exec_db.

Tactic Notation "rew" "bounded" := autorewrite with bounded_exec_db.
Tactic Notation "rew" "bounded" "in" hyp(H) := autorewrite with bounded_exec_db in H.

(** Extract the information about the numbering of events from relations in
bounded executions *)

Lemma bounded_sb_l (ex: Execution) (n: nat) (x y: Event):
  sb (bounded_exec ex n) x y ->
  numbering x <= n.
Proof.
  intros H. rew bounded in H. 
  apply simpl_trt_hyp in H as [H1 [_ H2]].
  unfold NLE in *. lia.
Qed.

Lemma bounded_sb_r (ex: Execution) (n: nat) (x y: Event):
  sb (bounded_exec ex n) x y ->
  numbering y <= n.
Proof.
  intros H. rew bounded in H. 
  apply simpl_trt_hyp in H as [H1 [_ H2]].
  unfold NLE in *. lia.
Qed.

Lemma bounded_rf_l (ex: Execution) (n: nat) (x y: Event):
  rf (bounded_exec ex n) x y ->
  numbering x <= n.
Proof.
  intros H. rew bounded in H. 
  apply simpl_trt_hyp in H as [H1 [_ H2]].
  unfold NLE in *. lia.
Qed.

Lemma bounded_rf_r (ex: Execution) (n: nat) (x y: Event):
  rf (bounded_exec ex n) x y ->
  numbering y <= n.
Proof.
  intros H. rew bounded in H. 
  apply simpl_trt_hyp in H as [H1 [_ H2]].
  unfold NLE in *. lia.
Qed.

Lemma bounded_mo_l (ex: Execution) (n: nat) (x y: Event):
  mo (bounded_exec ex n) x y ->
  numbering x <= n.
Proof.
  intros H. rew bounded in H. 
  apply simpl_trt_hyp in H as [H1 [_ H2]].
  unfold NLE in *. lia.
Qed.

Lemma bounded_mo_r (ex: Execution) (n: nat) (x y: Event):
  mo (bounded_exec ex n) x y ->
  numbering y <= n.
Proof.
  intros H. rew bounded in H. 
  apply simpl_trt_hyp in H as [H1 [_ H2]].
  unfold NLE in *. lia.
Qed.

Lemma bounded_rb_l (ex: Execution) (n: nat) (x y: Event):
  rb (bounded_exec ex n) x y ->
  numbering x <= n.
Proof.
  intros H. unfold rb in H. destruct H as [z H _]. 
  rewrite <-cnv_rev in H.
  rew bounded in H. 
  apply simpl_trt_hyp in H as [H1 [_ H2]].
  unfold NLE in *. lia.
Qed.

Lemma bounded_rb_r (ex: Execution) (n: nat) (x y: Event):
  rb (bounded_exec ex n) x y ->
  numbering y <= n.
Proof.
  intros H. unfold rb in H. destruct H as [z _ H].
  rew bounded in H. 
  apply simpl_trt_hyp in H as [H1 [_ H2]].
  unfold NLE in *. lia.
Qed.

(** An event belonging to the events of a bounded executions belong to the events
of the execution *)

Lemma bounding_evts_in (ex: Execution) (x: Event) (bound: nat):
  In _ (evts (bounded_exec ex bound)) x ->
  In _ (evts ex) x.
Proof.
  intros [y Hin _]. auto.
Qed.

(** Bounding two executions by the same bound maintains the prefix relationship
between them *)

Lemma bounding_of_prefix (pre ex: Execution) (bound: nat):
  prefix pre ex ->
  prefix (bounded_exec pre bound) (bounded_exec ex bound).
Proof.
  intros Hpre.
  inverse_prefix Hpre.
  repeat (apply conj).
  - rewrite simpl_evts_be. intros x H.
    apply in_intersection in H as [H1 H2].
    split.
    + apply Hevts in H1. auto.
    + unfold In in *. auto.
  - intros a b Hsbrf Hinb. specialize (Hclosed a b).
    split.
    + apply Hclosed.
      * destruct Hsbrf as [Hsbrf|Hsbrf];
        rew bounded in Hsbrf; 
        apply simpl_trt_rel in Hsbrf; [left|right]; auto.
      * rewrite simpl_evts_be in Hinb. apply in_intersection in Hinb as [Hinb _].
        auto.
    + unfold In.
      destruct Hsbrf as [Hsbrf|Hsbrf];
      apply simpl_trt_hyp in Hsbrf as [Hsbrf _];
      unfold NLE in Hsbrf; auto.
  - rew bounded. rewrite simpl_evts_be.
    rewrite I_inter. rewrite NLE_I_evts.
    rewrite Hsb. kat_eq.
  - rew bounded. rewrite simpl_evts_be.
    rewrite I_inter. rewrite NLE_I_evts.
    rewrite Hrf. kat_eq.
  - rew bounded. rewrite simpl_evts_be.
    rewrite I_inter. rewrite NLE_I_evts.
    rewrite Hmo. kat_eq.
  - rew bounded. rewrite simpl_evts_be.
    rewrite I_inter. rewrite NLE_I_evts.
    rewrite Hrmw. kat_eq.
Qed.

(** The union of all the relations of an execution bounded by [n] is included in
the union of all the relations of the execution bounded by [n] restricted to the
events whose numbering is less or equal to [n] *)

Lemma sc_cycle_be_incl_be_sc_cycle (ex: Execution) (n: nat):
  sb (bounded_exec ex n) ⊔
  rf (bounded_exec ex n) ⊔
  mo (bounded_exec ex n) ⊔
  rb (bounded_exec ex n) ≦
  [NLE n] ⋅
  (sb (bounded_exec ex n) ⊔
   rf (bounded_exec ex n) ⊔
   mo (bounded_exec ex n) ⊔
   rb (bounded_exec ex n) ) ⋅ [NLE n].
Proof.
  unfold rb.
  rew bounded.
  rewrite 2dot_cnv, injcnv.
  kat.
Qed.


(** The union of all the relations of a bounded execution is included in the
union of all the relations of the execution *)

Lemma cycle_be_incl_cycle_ex (ex: Execution) (bound:nat):
  sb (bounded_exec ex bound) ⊔ rf (bounded_exec ex bound) ⊔
  mo (bounded_exec ex bound) ⊔ rb (bounded_exec ex bound) ≦
  sb ex ⊔ rf ex ⊔ mo ex ⊔ rb ex.
Proof.
  unfold rb. rew bounded. rewrite 2dot_cnv, injcnv. kat.
Qed.

(** In a valid execution, if two events are related by [sb ex ⊔ rf ex], they 
belong to the events of [ex] *)

Lemma sbrf_in_events (ex: Execution) (x y : Event) :
  valid_exec ex ->
  ((sb ex) ⊔ (rf ex)) x y ->
  In _ (evts ex) x /\ In _ (evts ex) y.
Proof.
  intros Hval [Hsb | Hrf]; split;
  eauto using sb_orig_evts, sb_dest_evts, rf_orig_evts, rf_dest_evts.
Qed.

(** If an event belongs to the events of an execution bounded by [n], its 
numbering is less or equal to [n] and it belongs to the events of the execution *)

Lemma I_evts_bounded_le_bnd (ex: Execution) (n: nat):
  [I (evts (bounded_exec ex n))] = [NLE n] ⋅ [I (evts ex)].
Proof.
  apply ext_rel, antisym. 
  - intros x y [Heq Hinter]. destruct Hinter.
    exists x; split; auto.
  - intros x y [z [Heq Hr] [Heq1 Hr1]].
    rewrite <- Heq in Hr1. rewrite Heq1 in Heq.
    split; [|split]; auto.
Qed.

(** Any bounding of a valid execution is a prefix of this execution *)

Lemma bounded_exec_is_prefix (ex: Execution) (n: nat):
  valid_exec ex ->
  numbering_coherent ex ->
  prefix (bounded_exec ex n) ex.
Proof.
  intros Hval Hnumco.
  split; [|split].
  - apply intersection_included_itself.
  - intros x y Hnum.
    generalize (sbrf_in_events _ _ _ Hval Hnum); intros [Hx Hy].
    apply (Hnumco _ _) in Hnum.
    intros H. destruct H as [y Hevts Hbound]; split.
    + auto.
    + unfold_in; lia.
  - rew bounded.
    repeat (apply conj);
    destruct_val_exec Hval.
    + destruct_sb_v Hsb_v.
      destruct Hsb_lso as [Hsb_in_e _].
      rewrite Hsb_in_e, I_evts_bounded_le_bnd. kat_eq.
    + destruct_rf_v Hrf_v. rewrite Hrf_in_e, I_evts_bounded_le_bnd. kat_eq.
    + destruct_mo_v Hmo_v. destruct Hmopo as [Hmo_in_e _].
      rewrite Hmo_in_e, I_evts_bounded_le_bnd. kat_eq.
    + destruct_rmw_v Hrmw_v. rewrite Hrmw_in_e, I_evts_bounded_le_bnd. kat_eq.
Qed.

(** If an execution is valid, any of its boundings is valid *)

Lemma bounded_is_valid (ex: Execution) (bound: nat):
  valid_exec ex ->
  numbering_coherent ex ->
  valid_exec (bounded_exec ex bound).
Proof.
  intros Hval Hnumco.
  eapply prefix_valid.
  eauto.
  eapply bounded_exec_is_prefix;
  eauto.
Qed.

(** If an execution is complete, any of its boundings is complete *)

Lemma bounded_is_complete (ex: Execution) (bound: nat):
  complete_exec ex ->
  numbering_coherent ex ->
  complete_exec (bounded_exec ex bound).
Proof.
  intros Hcomp Hnumco.
  eapply prefix_complete.
  eauto.
  eapply bounded_exec_is_prefix; auto.
  destruct Hcomp as [Hval _]. auto.
Qed.

(** If an execution is consistent in the RC11 model, any of its boundings is 
consistent in the RC11 model *)

Lemma bounded_is_rc11 (ex: Execution) (bound: nat):
  valid_exec ex ->
  numbering_coherent ex ->
  rc11_consistent ex ->
  rc11_consistent (bounded_exec ex bound).
Proof.
  intros Hval Hnumco Hrc11.
  eapply prefix_rc11_consistent.
  eauto.
  eapply bounded_exec_is_prefix;
  eauto.
Qed.

(** If we have two boundings of an execution, the bounding bounded by the 
smallest bound is a prefix of the bounding bounded by the biggest bound *)

Lemma two_ord_bounds_pre (ex: Execution) (k1 k2: nat):
  valid_exec ex ->
  numbering_coherent ex ->
  k1 < k2 ->
  prefix (bounded_exec ex k1) (bounded_exec ex k2).
Proof.
  intros Hval Hnumco Hord.
  inverse_val_exec Hval.
  repeat (apply conj).
  - destruct ex. apply inter_incl. intros x.
    unfold In. intros H. lia.
  - intros a b [Hsb|Hrf] Hin; 
    apply in_intersection in Hin as [Hevts Hbord]; unfold_in.
    + rew bounded in Hsb. apply simpl_trt_hyp in Hsb as [_ [Hr _]].
      apply sb_num_ord in Hr as Habord; auto. split.
      * eapply sb_orig_evts; eauto.
      * unfold_in; lia.
    + rew bounded in Hrf. apply simpl_trt_hyp in Hrf as [_ [Hr _]].
      apply rf_num_ord in Hr as Habord; auto. split.
      * eapply rf_orig_evts; eauto.
      * unfold_in; lia.
  - rew bounded. rewrite I_evts_bounded_le_bnd.
    rewrite <- (nle_double _ _ Hord) at 1.
    rewrite <- (nle_double _ _ Hord) at 2.
    destruct_sb_v Hsb_v.
    destruct Hsb_lso as [Hsb_in_e _].
    rewrite Hsb_in_e. kat_eq.
  - rew bounded. rewrite I_evts_bounded_le_bnd.
    rewrite <- (nle_double _ _ Hord) at 1.
    rewrite <- (nle_double _ _ Hord) at 2.
    destruct_rf_v Hrf_v. rewrite Hrf_in_e. kat_eq.
  - rew bounded. rewrite I_evts_bounded_le_bnd.
    rewrite <- (nle_double _ _ Hord) at 1.
    rewrite <- (nle_double _ _ Hord) at 2.
    destruct_mo_v Hmo_v. destruct Hmopo as [Hmo_in_e _].
    rewrite Hmo_in_e. kat_eq.
  - rew bounded. rewrite I_evts_bounded_le_bnd.
    rewrite <- (nle_double _ _ Hord) at 1.
    rewrite <- (nle_double _ _ Hord) at 2.
    destruct_rmw_v Hrmw_v. rewrite Hrmw_in_e. kat_eq.
Qed.

(** There is a bound high enough so that the bounding of the execution is equal
to the execution *)

Lemma bounded_execution_itself_exists (ex: Execution):
  valid_exec ex ->
  exists k, ex = (bounded_exec ex k).
Proof.
  destruct (numbering_bounded) as [k Hsup].
  intros Hval.
  exists (numbering k).
  apply tautology_makes_fullset in Hsup. destruct ex.
  unfold bounded_exec. rew bounded.
  unfold NLE. rewrite Hsup. f_equal.
  - simpl. erewrite inter_fullset. auto.
  - unfold exec.sb. rewrite fullset_one. kat_eq.
  - unfold exec.rmw. rewrite fullset_one. kat_eq.
  - unfold exec.rf. rewrite fullset_one. kat_eq.
  - unfold exec.mo. rewrite fullset_one. kat_eq.
Qed.

(** ** Smallest conflicting prefix *)

(** A bound encodes the smallest possible conflicting prefix if all the other
conflicting boundings are bounded by a bigger bound *)

Definition smallest_conflicting_bounding (ex: Execution) (bound: nat) :=
  expi (bounded_exec ex bound) /\
  (forall n, expi (bounded_exec ex n) ->
             n >= bound).

Axiom smallest_conflicting_bounding_exists:
  forall ex, expi ex ->
             (exists bound, smallest_conflicting_bounding ex bound).

(** The boundings smaller than the smallest conflicting bounding are not 
conflicting *)

Lemma smaller_than_smallest_not_conflicting (ex: Execution) (bound: nat):
  (smallest_conflicting_bounding ex bound) ->
  forall smaller, smaller < bound -> 
                  ~(expi (bounded_exec ex smaller)).
Proof.
  intros [_ Hsmallest] smaller Hsmaller Hnot.
  apply Hsmallest in Hnot.
  lia.
Qed.

Theorem smaller_than_smallest_sc (ex: Execution) (bound: nat):
  valid_exec ex ->
  numbering_coherent ex ->
  rc11_consistent ex ->
  (smallest_conflicting_bounding ex bound) ->
  forall smaller, smaller < bound ->
                  sc_consistent (bounded_exec ex smaller).
Proof.
  intros Hval Hnumco Hrc11 Hscb smaller Hsmaller.
  eapply no_conflict_prefix_sc; eauto.
  - eauto using bounded_exec_is_prefix.
  - eapply smaller_than_smallest_not_conflicting; eauto.
Qed.

(** ** Minimal conflicting pair *)

(** If an execution contains conflicts, there is a unique pair of events that
are in conflict and belong to the smallest conflicting prefix of the execution *)

Definition minimal_conflicting_pair (ex: Execution) (bound: nat) (j k: Event) :=
  (smallest_conflicting_bounding ex bound) /\
  (pi (bounded_exec ex bound) j k).

(** Two events forming a minimal conflicting pair can be equal *)

Lemma mcp_irr (ex: Execution) (bound: nat) (k: Event):
  ~(minimal_conflicting_pair ex bound k k).
Proof.
  intros Hnot.
  destruct Hnot as [_ Hnot].
  apply pi_diff in Hnot.
  intuition auto.
Qed.

(** The minimal conflicting pair of given execution and bound is a symmetric
relation *)

Lemma mcp_is_sym (ex: Execution) (bound: nat) (j k: Event):
  (minimal_conflicting_pair ex bound j k) <->
  (minimal_conflicting_pair ex bound k j).
Proof. compute; intuition eauto. Qed.

(** The two events and the bound forming the minimal conflicting pair of an 
execution are such that the two events are pi-conflicting in the bounding of
the execution by the bound *)

Lemma mcp_is_pi (ex: Execution) (bound:nat) (j k: Event):
  minimal_conflicting_pair ex bound j k ->
  pi (bounded_exec ex bound) j k.
Proof. intros [_ ?]. auto. Qed.

(** The two events and the bound forming the minimal conflicting pair of an 
execution are such that the two events belong to the events of the bounding of
the execution by the bound *)

Lemma mcp_in_evts_left (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  In _ (evts (bounded_exec ex bound)) x.
Proof. intros. eauto using pi_in_evts_left, mcp_is_pi. Qed.

Lemma mcp_in_evts_right (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  In _ (evts (bounded_exec ex bound)) y.
Proof. intros. eauto using pi_in_evts_right, mcp_is_pi. Qed.

Lemma mcp_in_evts_left2 (ex: Execution) (x y: Event) (bound: nat):
  minimal_conflicting_pair ex bound x y ->
  In _ (evts ex) x.
Proof.
  intros Hmcp. apply mcp_in_evts_left in Hmcp.
  destruct Hmcp; auto.
Qed.

Lemma mcp_in_evts_right2 (ex: Execution) (x y: Event) (bound: nat):
  minimal_conflicting_pair ex bound x y ->
  In _ (evts ex) y.
Proof.
  intros Hmcp. apply mcp_in_evts_right in Hmcp.
  destruct Hmcp; auto.
Qed.
(** One of the two events forming a minimal conflicting pair must be a write 
event *)

Lemma mcp_one_is_write (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  is_write x \/ is_write y.
Proof. intros. eauto using pi_one_is_write, mcp_is_pi. Qed.

(** Two events forming a minimal conflicting pair are different *)

Lemma mcp_diff (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  x <> y.
Proof. intros. eauto using pi_diff, mcp_is_pi. Qed.

(** Two events forming a minimal conflicting pair affect the same location *)

Lemma mcp_same_loc (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  get_loc x = get_loc y.
Proof. intros. eauto using pi_same_loc, mcp_is_pi. Qed.

(** At least one of the two events forming a conflicting pair must be a SC
event *)

Lemma mcp_at_least_one_not_sc (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  at_least_one_not_sc x y.
Proof. intros. eauto using pi_at_least_one_not_sc, mcp_is_pi. Qed.

(** Two events forming a minimal conflicting pair must each be either a read or
a write *)

Lemma mcp_readwrite_l (ex: Execution) (x y: Event) (bound: nat):
  minimal_conflicting_pair ex bound x y ->
  (is_write x) \/ (is_read x).
Proof. intros. eauto using pi_readwrite_l, mcp_is_pi. Qed.

Lemma mcp_readwrite_r (ex: Execution) (x y: Event) (bound: nat):
  minimal_conflicting_pair ex bound x y ->
  (is_write y) \/ (is_read y).
Proof. intros. eauto using pi_readwrite_r, mcp_is_pi. Qed.

(** Two events forming a minimal conflicting pair are not ordered by the 
transitive closure of the union of the sequenced-before relation and of the
restriction of the reads-from relation to SC events, in the execution bounded
by the minimal bound in either direction *)

Lemma mcp_not_sbrfsc (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  ~((sb (bounded_exec ex bound) ⊔ (res_mode Sc (rf (bounded_exec ex bound))))^+ x y).
Proof. intros. eauto using pi_not_sbrfsc, mcp_is_pi. Qed.

Lemma mcp_not_cnv_sbrfsc (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  ~((sb (bounded_exec ex bound) ⊔ (res_mode Sc (rf (bounded_exec ex bound))))^+ y x).
Proof. intros. eauto using pi_not_cnv_sbrfsc, mcp_is_pi. Qed.

(** The events forming a minimal conflicting pair have a numbering less or equal
to the minimal bound *)

Lemma mcp_left_le_bound (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  (numbering x) <= bound.
Proof. 
  intros Hmcp. eapply mcp_in_evts_left in Hmcp.
  destruct Hmcp as [? _ Hxord]. unfold In in Hxord.
  auto.
Qed.

Lemma mcp_right_le_bound (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  (numbering y) <= bound.
Proof. 
  intros Hmcp. eapply mcp_in_evts_right in Hmcp.
  destruct Hmcp as [? _ Hxord]. unfold In in Hxord.
  auto.
Qed.

(** The numbering of one of the two events forming a minimal conflicting pair
is equal to the minimal bound and the numbering of the other event is strictly
inferior to the minmal bound *)

Lemma mcp_left_eq_lt_bound (ex: Execution) (bound: nat) (x y: Event):
  minimal_conflicting_pair ex bound x y ->
  (numbering x) = bound \/ (numbering x) < bound.
Proof.
  intros Hmcp.
  destruct (Compare_dec.lt_eq_lt_dec (numbering x) bound) as [[Hord|Hord]|Hord];
  [right;auto|left;auto|].
  apply mcp_left_le_bound in Hmcp. lia.
Qed.

Lemma mcp_right_eq_lt_bound (ex: Execution) (bound: nat) (x y: Event):
  minimal_conflicting_pair ex bound x y ->
  (numbering y) = bound \/ (numbering y) < bound.
Proof.
  intros Hmcp.
  destruct (Compare_dec.lt_eq_lt_dec (numbering y) bound) as [[Hord|Hord]|Hord];
  [right;auto|left;auto|].
  apply mcp_right_le_bound in Hmcp. lia.
Qed.

(** Every execution containing pi-conflicting events has a minimal conflicting
pair *)

Lemma mcp_exists (ex: Execution):
  expi ex ->
  (exists bound j k, minimal_conflicting_pair ex bound j k).
Proof.
  intros Hconf.
  destruct (smallest_conflicting_bounding_exists _ Hconf) as [bound Hsmallest].
  exists bound.
  destruct Hsmallest as [[j [k Hpreconf]] Hsmallest].
  exists j, k. split; [split|]; auto.
  exists j, k. auto.
Qed.

(** Every execution containing pi-conflicting events has a minimal conflicting
pair with one of the events having the biggest numbering *)

Lemma mcp_exists_ord (ex: Execution):
  expi ex ->
  numbering_injective ex ->
  (exists bound j k, minimal_conflicting_pair ex bound j k /\
                     (numbering j) < (numbering k)).
Proof.
  intros Hexpi Hnuminj.
  destruct (mcp_exists _ Hexpi) as [b [j [k Hmcp]]].
  destruct (Compare_dec.lt_eq_lt_dec (numbering j) (numbering k)) as
  [[Hcomp|Hcomp]|Hcomp].
  - exists b, j, k. intuition auto.
  - exfalso. eapply mcp_irr.
    eapply numbering_injective_eq in Hcomp; eauto.
    rewrite Hcomp in Hmcp. eauto.
  - exists b, k, j. intuition auto.
    eapply mcp_is_sym. auto.
Qed.

(** In a minimal conflicting pair, at least one of the two events is not SC *)

Lemma mcp_not_sc (ex: Execution) (bound: nat) (j k: Event):
  (minimal_conflicting_pair ex bound j k) ->
  ~((get_mode j) = Sc /\ (get_mode k) = Sc).
Proof.
  intros [_ [[_ H] _]].
  auto.
Qed.

(** In a minimal conflicting pair, the two conflicting events cannot be related
by sb *)

Lemma mcp_not_sb_jk (ex: Execution) (bound: nat) (j k: Event):
  minimal_conflicting_pair ex bound j k ->
  ~(sb ex j k).
Proof.
  intros Hmcp Hsb.
  inversion Hmcp as [_ [_ Hnot]].
  apply Hnot. left. apply tc_incl_itself. left.
  rew bounded. simpl_trt.
  - eapply mcp_left_le_bound. eauto.
  - auto.
  - eapply mcp_right_le_bound. eauto.
Qed.

(*
(** In a valid execution, the set of events whose numbering in an execution 
bounded by [n] is less or equal to a bound, is the same as the set of events
whose numbering in the execution is less or equal to the same bound *)

Lemma NLE_set_in_bound_ex_rew (ex: Execution) (b1 b2: nat):
  valid_exec ex ->
  (fun x => b2 >= (numbering x)) =
  (fun x => b2 >= (numbering x)).
Proof.
  intuition auto.
  intros Hval.
  pose proof (bounded_exec_is_prefix _ b1 Hval) as Hpre.
  pose proof (numbering_pre_stable _ _ Hpre) as Hnumeq.
  apply ext_set. split; intros H.
  - rewrite Hnumeq in H. auto.
  - rewrite Hnumeq. auto.
Qed.

Lemma NLE_in_bound_ex_rew (ex: Execution) (b1 b2: nat):
  valid_exec ex ->
  [NLE (bounded_exec ex b1) b2] = [NLE ex b2].
Proof.
  intros Hval.
  pose proof (bounded_exec_is_prefix _ b1 Hval) as Hpre.
  pose proof (numbering_pre_stable _ _ Hpre) as Hnumeq.
  apply ext_rel, antisym; intros x y H;
  destruct H as [Heq Hord];
  split; auto; unfold NLE in *.
  - rewrite Hnumeq in Hord; auto.
  - rewrite Hnumeq; auto.
Qed.
*)

(** Bounding an execution already bounded by a smaller bound has no effect *)

Lemma double_bounding_rew (ex: Execution) (b1 b2: nat):
  valid_exec ex ->
  b1 < b2 ->
  bounded_exec (bounded_exec ex b1) b2 = bounded_exec ex b1.
Proof.
  intros Hval Hord.
  unfold bounded_exec at 1.
  (*
  rewrite (NLE_in_bound_ex_rew _ b1 b2 Hval).
  rewrite (NLE_set_in_bound_ex_rew _ b1 b2 Hval).
  *)
  rew bounded. unfold bounded_exec at 2.
  f_equal.
  - apply ext_set. intros x; split; intros H.
    + destruct H as [y Hevtsb1 Hordb2].
      unfold bounded_exec in Hevtsb1.
      simpl in Hevtsb1. unfold In in Hevtsb1. auto.
    + split.
      * unfold bounded_exec. simpl. unfold In. auto.
      * destruct H as [y _ Hb1]. unfold_in. lia.
  - rewrite <- (nle_double _ _ Hord) at 4.
    rewrite <- (nle_double _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double _ _ Hord) at 4.
    rewrite <- (nle_double _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double _ _ Hord) at 4.
    rewrite <- (nle_double _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double _ _ Hord) at 4.
    rewrite <- (nle_double _ _ Hord) at 3.
    kat_eq.
Qed.

(** Bounding an execution already bounded with a greater bound is the same as
directly bounding the execution with the smaller bound *)

Lemma double_bounding_rew' (ex: Execution) (b1 b2: nat):
  valid_exec ex ->
  b1 < b2 ->
  bounded_exec (bounded_exec ex b2) b1 = bounded_exec ex b1.
Proof.
  intros Hval Hord.
  unfold bounded_exec at 1.
  (*
  rewrite (NLE_in_bound_ex_rew _ b2 b1 Hval).
  rewrite (NLE_set_in_bound_ex_rew _ b2 b1 Hval).
  *)
  rew bounded. unfold bounded_exec at 2.
  f_equal.
  - apply ext_set. intros x; split; intros H.
    + destruct H as [y Hevtsb2 Hb1].
      split; auto.
      destruct Hevtsb2; auto.
    + destruct H as [y Hevts Hb1].
      split; auto.
      split; auto.
      unfold_in; lia.
  - rewrite <- (nle_double _ _ Hord) at 4.
    rewrite <- (nle_double _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double _ _ Hord) at 4.
    rewrite <- (nle_double _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double _ _ Hord) at 4.
    rewrite <- (nle_double _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double _ _ Hord) at 4.
    rewrite <- (nle_double _ _ Hord) at 3.
    kat_eq.
Qed.

(** Bouding an execution twice with the same bound is the same as bounding it
once *)

Lemma double_same_bounding_rew (ex: Execution) (b: nat):
  valid_exec ex ->
  bounded_exec (bounded_exec ex b) b = bounded_exec ex b.
Proof.
  intros Hval.
  unfold bounded_exec at 3.
  unfold bounded_exec at 1.
  f_equal.
  - unfold bounded_exec at 1.
    unfold evts at 1.
    apply ext_set. intros x; split.
    + intros [y [H1 H2] H3]. split; unfold_in; auto.
    + intros [y H1 H2]. split; [split|]; unfold_in; auto.
  - rew bounded. kat_eq.
  - rew bounded. kat_eq.
  - rew bounded. kat_eq.
  - rew bounded. kat_eq.
Qed.

(** If a bound is the smallest conflicting bounding of an execution, it is the
smallest conflicting bounding of the execution bounded by the bound *)

Lemma scp_bounded (ex: Execution) (bound: nat):
  valid_exec ex ->
  smallest_conflicting_bounding ex bound ->
  smallest_conflicting_bounding (bounded_exec ex bound) bound.
Proof.
  intros Hval [Hexpi Hsmaller].
  split.
  - rewrite (double_same_bounding_rew ex bound Hval). auto.
  - intros n Hexpidbound.
    destruct (classic (n < bound)) as [Hord|Hord].
    + apply Hsmaller. erewrite double_bounding_rew' in Hexpidbound; auto.
    + apply Compare_dec.not_lt in Hord. auto.
Qed.

(** If two events and a bound are the minimal conflicting pair of an execution,
they are the minimal conflicting pair of the execution bounded by the bound *)

Lemma mcp_bounded (ex: Execution) (bound: nat) (x y: Event):
  valid_exec ex ->
  minimal_conflicting_pair ex bound x y ->
  minimal_conflicting_pair (bounded_exec ex bound) bound x y.
Proof.
  intros Hval [Hscb Hpi]; split.
  - apply scp_bounded; auto.
  - rewrite (double_same_bounding_rew ex bound Hval). auto.
Qed.

(** If two events are conflicting in a bounded execution, they are also 
conflicting in the execution bounded by the greatest of the numberings of the
two events *)

Lemma bound_to_c_events (ex: Execution) (b:nat) (j k: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering j <= numbering k ->
  numbering k < b ->
  pi (bounded_exec ex b) j k ->
  pi (bounded_exec ex (numbering k)) j k.
Proof.
  intros Hval Hnumco Hord Hord' [[[Hinj [Hink [Hw [Hdiff Hloc]]]] Hsc] Hbidir].
  repeat (apply conj); auto.
  - destruct ex. simpl. destruct Hinj as [z Hjevts Hinj]. split.
    + simpl in Hjevts. auto.
    + unfold In. lia.
  - destruct ex. simpl. destruct Hink as [z Hkevts Hink]. split.
    + simpl in Hkevts. auto.
    + unfold In. lia.
  (*
  - destruct (not_or_and _ _ Hbidir) as [Hjk Hkj].
    apply and_not_or. split; auto.
  *)
  - destruct (not_or_and _ _ Hbidir) as [Hjk Hkj].
    intros Hnot. destruct Hnot as [Hnot|Hnot].
    + apply Hjk.
      eapply sbrfsc_pre_inc.
      * eapply two_ord_bounds_pre; eauto.
      * auto.
    + apply Hkj.
      eapply sbrfsc_pre_inc.
      * eapply two_ord_bounds_pre; eauto.
      * auto.
Qed.

(** If two events are conflicting and if their numbering is strictly inferior to
a bound, this bound cannot be the smallest conflicting bounding *)

Lemma smallest_conflicting_bounding_conflict (ex: Execution) (j k: Event) (b: nat):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering k < b ->
  numbering j < b ->
  smallest_conflicting_bounding ex b ->
  pi (bounded_exec ex b) j k ->
  False.
Proof.
  intros Hval Hnumco Hord1 Hord2 Hscb Hconf.
  destruct (Compare_dec.lt_eq_lt_dec (numbering j) (numbering k)) as [[Hjlt|Hjeq]|Hjgt].
  - destruct Hscb as [_ Hsmallest].
    assert (numbering k >= b).
    * apply Hsmallest. exists j, k.
      apply bound_to_c_events with b; auto. lia.
    * lia.
  - destruct Hscb as [_ Hsmallest].
    assert (numbering k >= b).
    * apply Hsmallest. exists j, k.
      apply bound_to_c_events with b; auto. lia.
    * lia.
  - destruct Hscb as [_ Hsmallest].
    assert (numbering j >= b).
    * apply Hsmallest. exists j, k.
      rewrite pi_sym. rewrite pi_sym in Hconf.
      apply bound_to_c_events with b; auto. lia.
    * lia.
Qed.

(** In a minimal conflicting pair, the bound is the numbering of one of the two
conflicting events *)

Theorem mcp_num_snd_evt (ex: Execution) (bound: nat) (j k: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  (minimal_conflicting_pair ex bound j k) ->
  (max (numbering k) (numbering j) = bound).
Proof.
  intros Hval Hnumco [Hscb Hconf].
  destruct (Compare_dec.lt_eq_lt_dec bound (numbering k)) as [[Hklt|Hkeq]|Hkgt].
  - destruct Hconf as [[[_ [? _]] _] _]. destruct ex. simpl in H.
    destruct H as [? ?]. unfold In in *. lia.
  - destruct (Compare_dec.lt_eq_lt_dec (numbering j) (numbering k)) as [[Hjlt|Hjeq]|Hjgt].
    + rewrite (max_rewrite _ _ Hjlt). auto.
    + rewrite Hjeq, PeanoNat.Nat.max_id. auto.
    + destruct Hconf as [[[? _] _] _].
      destruct ex. simpl in H. destruct H as [? ?]. unfold In in *. lia.
  - destruct (Compare_dec.lt_eq_lt_dec (numbering j) (numbering k)) as [[Hjlt|Hjeq]|Hjgt].
    + exfalso. 
      apply (smallest_conflicting_bounding_conflict ex j k bound); auto.
      lia.
    + exfalso.
      apply (smallest_conflicting_bounding_conflict ex j k bound); auto.
      lia.
    + rewrite (max_rewrite' _ _ Hjgt).
      destruct (Compare_dec.lt_eq_lt_dec (numbering j) bound) as [[Hblt|Hbeq]|Hbgt].
      * exfalso.
        apply (smallest_conflicting_bounding_conflict ex j k bound); auto.
      * auto.
      * destruct Hconf as [[[? _] _] _]. destruct ex. simpl in H.
        destruct H as [? ?]. unfold In in *. lia.
Qed.

Lemma mcp_num_snd_evt_ord (ex: Execution) (bound: nat) (j k: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  (minimal_conflicting_pair ex bound j k) ->
  (numbering k) > (numbering j) ->
  numbering k = bound.
Proof.
  intros Hval Hnumco Hmcp Hord.
  pose proof (mcp_num_snd_evt _ _ _ _ Hval Hnumco Hmcp) as Hmax.
  rewrite (max_rewrite _ _ Hord) in Hmax. auto.
Qed.

(** All the events of a minimal conflicting pair that are not the second event
of the pair have a numbering smaller than the second event *)

Lemma mcp_all_smaller_snd_evt (ex: Execution) (bound: nat) (x j k: Event):
  valid_exec ex ->
  numbering_coherent ex ->
  numbering_injective ex ->
  (minimal_conflicting_pair ex bound j k) ->
  (numbering k) > (numbering j) ->
  In _ (evts (bounded_exec ex bound)) x ->
  x <> k ->
  numbering x < numbering k.
Proof.
  intros Hval Hnumco Hnuminj Hmcp Hord Hxevts Hdiff.
  pose proof (mcp_num_snd_evt_ord _ _ _ _ Hval Hnumco Hmcp Hord) as Heq.
  apply in_intersection in Hxevts as [_ Hxbound].
  unfold In in Hxbound. rewrite Heq.
  destruct (Compare_dec.lt_eq_lt_dec (numbering x) bound) as [[H|H]|H].
  - lia.
  - rewrite <-H in Heq. apply (numbering_injective_eq _ _ _ Hnuminj) in Heq.
    congruence.
  - lia.
Qed.














  