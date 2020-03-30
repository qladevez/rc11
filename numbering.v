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

Module Type Numbering.

Parameter numbering : Execution -> (Event -> nat).

Axiom numbering_injective: forall ex x y, 
  x <> y <-> numbering ex x <> numbering ex y.

Lemma numbering_injective_eq (ex: Execution) (x y: Event):
  x = y <-> numbering ex x = numbering ex y.
Proof.
  split; intros H.
  - rewrite H; auto.
  - destruct (classic (x = y)) as [Hxy | Hxy].
    + auto.
    + rewrite (numbering_injective ex x y) in Hxy.
      destruct (Hxy H).
Qed.

Axiom numbering_coherent: 
  forall ex x y, ((sb ex) ⊔ (rf ex)) x y ->
                 numbering ex x < numbering ex y.

Lemma numbering_coherent_rtc (ex: Execution) (x y: Event):
  ((sb ex) ⊔ (rf ex))^* x y ->
  numbering ex y >= numbering ex x.
Proof.
  generalize x y.
  clear x y.
  apply rtc_ind.
  - intros x y Hstep. apply numbering_coherent in Hstep. lia.
  - auto.
  - intros x y z _ IH1 _ IH2. lia.
Qed.

Lemma numbering_coherent_tc (ex: Execution) (x y: Event):
  ((sb ex) ⊔ (rf ex))^+ x y ->
  numbering ex y > numbering ex x.
Proof.
  intros [z Hstep Hrtc].
  apply numbering_coherent in Hstep.
  apply numbering_coherent_rtc in Hrtc.
  lia.
Qed.

Lemma sb_num_ord (ex: Execution) (x y: Event):
  sb ex x y ->
  (numbering ex y) >= (numbering ex x).
Proof.
  intros Hsb.
  apply numbering_coherent_rtc, rtc_incl_itself.
  left; auto.
Qed.

Lemma rf_num_ord (ex: Execution) (x y: Event):
  rf ex x y ->
  (numbering ex y) >= (numbering ex x).
Proof.
  intros Hsb.
  apply numbering_coherent_rtc, rtc_incl_itself.
  right; auto.
Qed.

(** In every execution, there is a last event whose numbering is greater than
the one of all the other events *)

Axiom numbering_bounded :
  forall ex, { e | forall x, numbering ex e >= numbering ex x}.

Definition has_number (ex: Execution) (e: Event) (k:nat) : Prop :=
  numbering ex e = k.


(** If an execution is a prefix of the other, the events that are in the prefix
have the same numbering in the execution and in the prefix *)

Axiom numbering_pre_stable:
  forall pre ex, prefix pre ex -> (forall e, numbering pre e = numbering ex e).

End Numbering.

Module NumberingPrefix (Numbering: Numbering).

Import Numbering.

(** Tests if the numbering of an event is Less or Equal to a bound *)

Definition NLE (ex: Execution) (b: nat) : prop_set Event :=
  fun e => b >= (numbering ex e).

Lemma nle_double (ex: Execution) (k1 k2: nat):
  k1 < k2 ->
  [NLE ex k1]⋅[NLE ex k2] = [NLE ex k1].
Proof.
  intros Hord. apply ext_rel, antisym.
  - intros x y [z [Heq1 Hr1] [Heq2 Hr2]].
    rewrite Heq2 in Heq1, Hr2. split; auto.
  - intros x y [Heq Hr].
    exists x; split; auto.
    unfold NLE in Hr. unfold NLE. lia.
Qed.

Definition bounded_exec (ex: Execution) (n: nat) : Execution :=
  {|
    exec.evts := Intersection _ (evts ex) (fun x => n >= numbering ex x);
    exec.sb := [NLE ex n] ⋅ (sb ex) ⋅ [NLE ex n];
    exec.rmw := [NLE ex n] ⋅ (rmw ex) ⋅ [NLE ex n];
    exec.rf := [NLE ex n] ⋅ (rf ex) ⋅ [NLE ex n];
    exec.mo := [NLE ex n] ⋅  (mo ex) ⋅ [NLE ex n];
  |}.

Lemma simpl_sb_be (ex: Execution) (n:nat):
  sb (bounded_exec ex n) = [NLE ex n] ⋅ (sb ex) ⋅ [NLE ex n].
Proof. compute; auto. Qed.

Lemma simpl_rmw_be (ex: Execution) (n:nat):
  rmw (bounded_exec ex n) = [NLE ex n] ⋅ (rmw ex) ⋅ [NLE ex n].
Proof. compute; auto. Qed.

Lemma simpl_rf_be (ex: Execution) (n:nat):
  rf (bounded_exec ex n) = [NLE ex n] ⋅ (rf ex) ⋅ [NLE ex n].
Proof. compute; auto. Qed.

Lemma simpl_mo_be (ex: Execution) (n:nat):
  mo (bounded_exec ex n) = [NLE ex n] ⋅ (mo ex) ⋅ [NLE ex n].
Proof. compute; auto. Qed.

Create HintDb bounded_exec_db.

Hint Rewrite simpl_sb_be simpl_rmw_be simpl_rf_be simpl_mo_be : bounded_exec_db.

Tactic Notation "rew" "bounded" := autorewrite with bounded_exec_db.
Tactic Notation "rew" "bounded" "in" hyp(H) := autorewrite with bounded_exec_db in H.

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

Lemma I_evts_bounded_le_bnd (ex: Execution) (n: nat):
  [I (evts (bounded_exec ex n))] = [NLE ex n] ⋅ [I (evts ex)].
Proof.
  apply ext_rel, antisym. 
  - intros x y [Heq Hinter]. destruct Hinter.
    exists x; split; auto.
  - intros x y [z [Heq Hr] [Heq1 Hr1]].
    rewrite <- Heq in Hr1. rewrite Heq1 in Heq.
    split; [|split]; auto.
Qed.

(** Any bounding of a valid execution is a prefix of this execution *)

Lemma bounded_exec_is_prefix (ex: Execution) (n: nat) :
  valid_exec ex ->
  prefix (bounded_exec ex n) ex.
Proof.
  intros Hval.
  split; [|split].
  - apply intersection_included_itself.
  - intros x y Hnum.
    generalize (sbrf_in_events _ _ _ Hval Hnum); intros [Hx Hy].
    apply (numbering_coherent _ _ _) in Hnum.
    intros H. destruct H as [y Hevts Hbound]; split.
    + auto.
    + unfold_in; lia.
  - rew bounded.
    repeat (apply conj);
    destruct_val_exec Hval.
    + destruct_sb_v Hsb_v. rewrite Hsb_in_e, I_evts_bounded_le_bnd. kat_eq.
    + destruct_rf_v Hrf_v. rewrite Hrf_in_e, I_evts_bounded_le_bnd. kat_eq.
    + destruct_mo_v Hmo_v. destruct Hmopo as [Hmo_in_e _].
      rewrite Hmo_in_e, I_evts_bounded_le_bnd. kat_eq.
    + destruct_rmw_v Hrmw_v. rewrite Hrmw_in_e, I_evts_bounded_le_bnd. kat_eq.
Qed.

(** If we have to boundings of an execution, the smallest is a prefix of the
biggest *)

Lemma two_ord_bounds_pre (ex: Execution) (k1 k2: nat):
  valid_exec ex ->
  k1 < k2 ->
  prefix (bounded_exec ex k1) (bounded_exec ex k2).
Proof.
  intros Hval Hord.
  inverse_val_exec Hval.
  repeat (apply conj).
  - destruct ex. apply inter_incl. intros x.
    unfold In. intros H. lia.
  - intros a b [Hsb|Hrf] Hin; 
    apply in_intersection in Hin as [Hevts Hbord]; unfold_in.
    + rew bounded in Hsb. apply simpl_trt_hyp in Hsb as [_ [Hr _]].
      apply sb_num_ord in Hr as Habord. split.
      * eapply sb_orig_evts; eauto.
      * unfold_in; lia.
    + rew bounded in Hrf. apply simpl_trt_hyp in Hrf as [_ [Hr _]].
      apply rf_num_ord in Hr as Habord. split.
      * eapply rf_orig_evts; eauto.
      * unfold_in; lia.
  - rew bounded. rewrite I_evts_bounded_le_bnd.
    rewrite <- (nle_double ex _ _ Hord) at 1.
    rewrite <- (nle_double ex _ _ Hord) at 2.
    destruct_sb_v Hsb_v. rewrite Hsb_in_e. kat_eq.
  - rew bounded. rewrite I_evts_bounded_le_bnd.
    rewrite <- (nle_double ex _ _ Hord) at 1.
    rewrite <- (nle_double ex _ _ Hord) at 2.
    destruct_rf_v Hrf_v. rewrite Hrf_in_e. kat_eq.
  - rew bounded. rewrite I_evts_bounded_le_bnd.
    rewrite <- (nle_double ex _ _ Hord) at 1.
    rewrite <- (nle_double ex _ _ Hord) at 2.
    destruct_mo_v Hmo_v. destruct Hmopo as [Hmo_in_e _].
    rewrite Hmo_in_e. kat_eq.
  - rew bounded. rewrite I_evts_bounded_le_bnd.
    rewrite <- (nle_double ex _ _ Hord) at 1.
    rewrite <- (nle_double ex _ _ Hord) at 2.
    destruct_rmw_v Hrmw_v. rewrite Hrmw_in_e. kat_eq.
Qed.

(** There is a bound high enough so that the bounding of the execution 
corresponds to the execution *)

Lemma bounded_execution_itself_exists (ex: Execution):
  valid_exec ex ->
  exists k, ex = (bounded_exec ex k).
Proof.
  destruct (numbering_bounded ex) as [k Hsup].
  intros Hval.
  exists (numbering ex k).
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
bounds producing a conflicting prefix are bigger *)

Definition smallest_conflicting_bounding (ex: Execution) (bound: nat) :=
  expi (bounded_exec ex bound) /\
  (forall n, expi (bounded_exec ex n) ->
             n >= bound).

Axiom smallest_conflicting_bounding_exists:
  forall ex, expi ex ->
             (exists bound, smallest_conflicting_bounding ex bound).

(** The bounding smaller than the smallest conflicting bounding are not 
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
  rc11_consistent ex ->
  (smallest_conflicting_bounding ex bound) ->
  forall smaller, smaller < bound ->
                  sc_consistent (bounded_exec ex smaller).
Proof.
  intros Hval Hrc11 Hscb smaller Hsmaller. 
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

Lemma mcp_is_pi (ex: Execution) (bound:nat) (j k: Event):
  minimal_conflicting_pair ex bound j k ->
  pi (bounded_exec ex bound) j k.
Proof. intros [_ ?]. auto. Qed.

Lemma mcp_in_evts_left (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  In _ (evts (bounded_exec ex bound)) x.
Proof. intros. eauto using pi_in_evts_left, mcp_is_pi. Qed.

Lemma mcp_in_evts_right (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  In _ (evts (bounded_exec ex bound)) y.
Proof. intros. eauto using pi_in_evts_right, mcp_is_pi. Qed.

Lemma mcp_one_is_write (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  is_write x \/ is_write y.
Proof. intros. eauto using pi_one_is_write, mcp_is_pi. Qed.

Lemma mcp_diff (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  x <> y.
Proof. intros. eauto using pi_diff, mcp_is_pi. Qed.

Lemma mcp_same_loc (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  get_loc x = get_loc y.
Proof. intros. eauto using pi_same_loc, mcp_is_pi. Qed.

Lemma mcp_at_least_one_sc (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  at_least_one_sc x y.
Proof. intros. eauto using pi_at_least_one_sc, mcp_is_pi. Qed.

Lemma mcp_not_sbrfsc (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  ~((sb (bounded_exec ex bound) ⊔ (res_mode Sc (rf (bounded_exec ex bound))))^+ x y).
Proof. intros. eauto using pi_not_sbrfsc, mcp_is_pi. Qed.

Lemma mcp_not_cnv_sbrfsc (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  ~((sb (bounded_exec ex bound) ⊔ (res_mode Sc (rf (bounded_exec ex bound))))^+ y x).
Proof. intros. eauto using pi_not_cnv_sbrfsc, mcp_is_pi. Qed.

Lemma mcp_left_le_bound (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) <= bound.
Proof. 
  intros Hmcp. eapply mcp_in_evts_left in Hmcp.
  destruct Hmcp as [? _ Hxord]. unfold In in Hxord.
  auto.
Qed.

Lemma mcp_right_le_bound (ex: Execution) (x y: Event) (bound:nat):
  minimal_conflicting_pair ex bound x y ->
  (numbering ex y) <= bound.
Proof. 
  intros Hmcp. eapply mcp_in_evts_right in Hmcp.
  destruct Hmcp as [? _ Hxord]. unfold In in Hxord.
  auto.
Qed.

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

(** In a minimal conflicting pair, at least one of the two events is not SC *)

Lemma mcp_not_sc (ex: Execution) (bound: nat) (j k: Event):
  (minimal_conflicting_pair ex bound j k) ->
  ((get_mode j) <> Sc \/ (get_mode k) <> Sc).
Proof.
  intros [_ [[_ H] _]].
  auto.
Qed.

Lemma NLE_set_in_bound_ex_rew (ex: Execution) (b1 b2: nat):
  valid_exec ex ->
  (fun x => b2 >= (numbering (bounded_exec ex b1) x)) =
  (fun x => b2 >= (numbering ex x)).
Proof.
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

(** Bounding an execution already bounded by a smaller bound has no effect *)

Lemma double_bounding_rew (ex: Execution) (b1 b2: nat):
  valid_exec ex ->
  b1 < b2 ->
  bounded_exec (bounded_exec ex b1) b2 = bounded_exec ex b1.
Proof.
  intros Hval Hord.
  unfold bounded_exec at 1.
  rewrite (NLE_in_bound_ex_rew _ b1 b2 Hval).
  rewrite (NLE_set_in_bound_ex_rew _ b1 b2 Hval).
  rew bounded. unfold bounded_exec at 2.
  f_equal.
  - apply ext_set. intros x; split; intros H.
    + destruct H as [y Hevtsb1 Hordb2].
      unfold bounded_exec in Hevtsb1.
      simpl in Hevtsb1. unfold In in Hevtsb1. auto.
    + split.
      * unfold bounded_exec. simpl. unfold In. auto.
      * destruct H as [y _ Hb1]. unfold_in. lia.
  - rewrite <- (nle_double ex _ _ Hord) at 4.
    rewrite <- (nle_double ex _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double ex _ _ Hord) at 4.
    rewrite <- (nle_double ex _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double ex _ _ Hord) at 4.
    rewrite <- (nle_double ex _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double ex _ _ Hord) at 4.
    rewrite <- (nle_double ex _ _ Hord) at 3.
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
  rewrite (NLE_in_bound_ex_rew _ b2 b1 Hval).
  rewrite (NLE_set_in_bound_ex_rew _ b2 b1 Hval).
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
  - rewrite <- (nle_double ex _ _ Hord) at 4.
    rewrite <- (nle_double ex _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double ex _ _ Hord) at 4.
    rewrite <- (nle_double ex _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double ex _ _ Hord) at 4.
    rewrite <- (nle_double ex _ _ Hord) at 3.
    kat_eq.
  - rewrite <- (nle_double ex _ _ Hord) at 4.
    rewrite <- (nle_double ex _ _ Hord) at 3.
    kat_eq.
Qed.

(** If two events are conflicting in a bounded execution, they are also 
conflicting in the execution bounded by the greatest of the numberings of the
two events *)

Lemma bound_to_c_events (ex: Execution) (b:nat) (j k: Event):
  valid_exec ex ->
  numbering ex j <= numbering ex k ->
  numbering ex k < b ->
  pi (bounded_exec ex b) j k ->
  pi (bounded_exec ex (numbering ex k)) j k.
Proof.
  intros Hval Hord Hord' [[[Hinj [Hink [Hw [Hdiff Hloc]]]] Hsc] Hbidir].
  repeat (apply conj).
  - destruct ex. simpl. destruct Hinj as [z Hjevts Hinj]. split.
    + simpl in Hjevts. auto.
    + unfold In. lia.
  - destruct ex. simpl. destruct Hink as [z Hkevts Hink]. split.
    + simpl in Hkevts. auto.
    + unfold In. lia.
  - auto.
  - auto.
  - auto.
  - auto.
  - destruct (not_or_and _ _ Hbidir) as [Hjk Hkj].
    apply and_not_or. split.
    + intros Hnot. apply Hjk.
      eapply sbrfsc_pre_inc.
      * eapply two_ord_bounds_pre; eauto.
      * auto.
    + intros Hnot. apply Hkj. 
      eapply sbrfsc_pre_inc.
      * eapply two_ord_bounds_pre; eauto.
      * auto.
Qed.

(** If two events are conflicting and if their numbering is strictly inferior to
a bound, this bound cannot be the smallest conflicting bounding *)

Lemma smallest_conflicting_bounding_conflict (ex: Execution) (j k: Event) (b: nat):
  valid_exec ex ->
  numbering ex k < b ->
  numbering ex j < b ->
  smallest_conflicting_bounding ex b ->
  pi (bounded_exec ex b) j k ->
  False.
Proof.
  intros Hval Hord1 Hord2 Hscb Hconf.
  destruct (Compare_dec.lt_eq_lt_dec (numbering ex j) (numbering ex k)) as [[Hjlt|Hjeq]|Hjgt].
  - destruct Hscb as [_ Hsmallest].
    assert (numbering ex k >= b).
    * apply Hsmallest. exists j, k.
      apply bound_to_c_events with b; auto. lia.
    * lia.
  - destruct Hscb as [_ Hsmallest].
    assert (numbering ex k >= b).
    * apply Hsmallest. exists j, k.
      apply bound_to_c_events with b; auto. lia.
    * lia.
  - destruct Hscb as [_ Hsmallest].
    assert (numbering ex j >= b).
    * apply Hsmallest. exists j, k.
      rewrite pi_sym. rewrite pi_sym in Hconf.
      apply bound_to_c_events with b; auto. lia.
    * lia.
Qed.

(** In a minimal conflicting pair, the bound is the numbering of one of the two
conflicting events *)

Theorem mcp_num_snd_evt (ex: Execution) (bound: nat) (j k: Event):
  valid_exec ex ->
  (minimal_conflicting_pair ex bound j k) ->
  (max (numbering ex k) (numbering ex j) = bound).
Proof.
  intros Hval [Hscb Hconf].
  destruct (Compare_dec.lt_eq_lt_dec bound (numbering ex k)) as [[Hklt|Hkeq]|Hkgt].
  - destruct Hconf as [[[_ [? _]] _] _]. destruct ex. simpl in H.
    destruct H as [? ?]. unfold In in *. lia.
  - destruct (Compare_dec.lt_eq_lt_dec (numbering ex j) (numbering ex k)) as [[Hjlt|Hjeq]|Hjgt].
    + rewrite (max_rewrite _ _ Hjlt). auto.
    + rewrite Hjeq, PeanoNat.Nat.max_id. auto.
    + destruct Hconf as [[[? _] _] _].
      destruct ex. simpl in H. destruct H as [? ?]. unfold In in *. lia.
  - destruct (Compare_dec.lt_eq_lt_dec (numbering ex j) (numbering ex k)) as [[Hjlt|Hjeq]|Hjgt].
    + exfalso. 
      apply (smallest_conflicting_bounding_conflict ex j k bound); auto.
      lia.
    + exfalso.
      apply (smallest_conflicting_bounding_conflict ex j k bound); auto.
      lia.
    + rewrite (max_rewrite' _ _ Hjgt).
      destruct (Compare_dec.lt_eq_lt_dec (numbering ex j) bound) as [[Hblt|Hbeq]|Hbgt].
      * exfalso.
        apply (smallest_conflicting_bounding_conflict ex j k bound); auto.
      * auto.
      * destruct Hconf as [[[? _] _] _]. destruct ex. simpl in H.
        destruct H as [? ?]. unfold In in *. lia.
Qed.

End NumberingPrefix.