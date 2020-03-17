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
From RC11 Require Import prefix.
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

Definition bounded_exec (ex: Execution) (n: nat) : Execution :=
  let new_evts := Intersection _ (evts ex) (fun x => n >= numbering ex x) in
  {|
    evts := new_evts;
    sb := res_eset new_evts (sb ex);
    rmw := res_eset new_evts (rmw ex);
    rf := res_eset new_evts (rf ex);
    mo := res_eset new_evts (mo ex);
  |}.


(** In a valid execution, if two events are related by [sb ex ⊔ rf ex], they 
belong to the events of [ex] *)

Lemma sbrf_in_events (ex: Execution) (x y : Event) :
  valid_exec ex ->
  ((sb ex) ⊔ (rf ex)) x y ->
  In _ (evts ex) x /\
  In _ (evts ex) y.
Proof.
  intros Hval [Hsb | Hrf]; split;
  eauto using sb_orig_evts, sb_dest_evts, rf_orig_evts, rf_dest_evts.
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
    + unfold In in *; lia.
  - auto.
Qed.

(** If we have to boundings of an execution, the smallest is a prefix of the
biggest *)

Lemma two_ord_bounds_pre (ex: Execution) (k1 k2: nat):
  k1 < k2 ->
  prefix (bounded_exec ex k1) (bounded_exec ex k2).
Proof.
  intros Hord.
  repeat (apply conj); simpl.
  - destruct ex. apply inter_incl. intros x.
    unfold In. intros H. lia.
  - intros a b [Hsb|Hsb] Hin;
    apply res_eset_incl in Hsb as Hrel;
    apply res_eset_elt_left in Hsb as Hsb;
    unfold In in *; apply Intersection_intro; unfold In in *.
    1,3: destruct Hsb; auto.
    + destruct Hin; unfold In in *;
      assert (numbering ex x >= numbering ex a).
      { apply numbering_coherent_rtc. apply rtc_incl_itself.
        left; auto. }
      lia.
    + destruct Hin; unfold In in *.
      assert (numbering ex x >= numbering ex a).
      apply numbering_coherent_rtc. apply rtc_incl_itself.
      right; auto.
      lia.
  - rewrite res_eset_double'; auto;
    intros x [H1 H2]; split; auto;
    unfold In in *; lia.
  - rewrite res_eset_double'; auto;
    intros x [H1 H2]; split; auto;
    unfold In in *; lia.
  - rewrite res_eset_double'; auto;
    intros x [H1 H2]; split; auto;
    unfold In in *; lia.
  - rewrite res_eset_double'; auto;
    intros x [H1 H2]; split; auto;
    unfold In in *; lia.
Qed.

(** There is a bound high enough so that the bounding of the execution 
corresponds to the execution *)

Lemma bounded_execution_itself_exists (ex: Execution):
  valid_exec ex ->
  exists k, ex = (bounded_exec ex k).
Proof.
  destruct (numbering_bounded ex) as [k Hsup].
  exists (numbering ex k). destruct ex.
  unfold bounded_exec. f_equal; simpl;
  destruct_val_exec H;
  rewrite (tautology_makes_fullset _ Hsup), inter_fullset.
  - auto.
  - destruct_sb_v Hsb_v. simpl in *.
    auto using res_eset_udr.
  - destruct_rmw_v Hrmw_v. simpl in *.
    auto using res_eset_udr.
  - destruct_rf_v Hrf_v. simpl in *.
    auto using res_eset_udr.
  - destruct_mo_v Hmo_v. simpl in *.
    destruct Hmopo as [? _].
    auto using res_eset_udr.
Qed.

(** ** Smallest conflicting prefix *)

(** A bound encodes the smallest possible conflicting prefix if all the other
bounds producing a conflicting prefix are bigger *)

Definition smallest_conflicting_bounding (ex: Execution) (bound: nat) :=
  conflicting (bounded_exec ex bound) /\
  (forall n, conflicting (bounded_exec ex n) ->
             n >= bound).

Axiom smallest_conflicting_bounding_exists:
  forall ex, conflicting ex ->
             (exists bound, smallest_conflicting_bounding ex bound).

(** The bounding smaller than the smallest conflicting bounding are not 
conflicting *)

Lemma smaller_than_smallest_not_conflicting (ex: Execution) (bound: nat):
  (smallest_conflicting_bounding ex bound) ->
  forall smaller, smaller < bound -> 
                  ~(conflicting (bounded_exec ex smaller)).
Proof.
  intros [_ Hsmallest] smaller Hsmaller Hnot.
  apply Hsmallest in Hnot.
  lia.
Qed.

(** ** Minimal conflicting pair *)

(** If an execution contains conflicts, there is a unique pair of events that
are in conflict and belong to the smallest conflicting prefix of the execution *)

Definition minimal_conflicting_pair (ex: Execution) (bound: nat) (j k: Event) :=
  (smallest_conflicting_bounding ex bound) /\
  (c_events (bounded_exec ex bound) j k).

Lemma mcp_exists (ex: Execution):
  conflicting ex ->
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
  intros [_ [[H | H] _]]; [left|right]; auto.
Qed.

(** Bounding an execution already bounded by a smaller bound has no effect *)

Lemma double_bounding_rew (ex: Execution) (b1 b2: nat):
  valid_exec ex ->
  b1 < b2 ->
  bounded_exec (bounded_exec ex b1) b2 = bounded_exec ex b1.
Proof.
  intros Hval Hord.
  pose proof (bounded_exec_is_prefix _ b1 Hval) as Hpre.
  pose proof (numbering_pre_stable _ _ Hpre) as Hnumeq.
  destruct ex. unfold bounded_exec. unfold bounded_exec in Hnumeq.
  simpl exec.evts in Hnumeq. simpl exec.evts. f_equal.
  - apply ext_set. split.
    + intros [? ?]. auto.
    + intros ?. split. 
      * auto.
      * cbv in Hnumeq. cbv. erewrite Hnumeq. destruct H as [? ?].
        unfold In in H0. lia.
  - apply ext_rel. split.
    + intros [? [? ?]]. auto.
    + intros [[? ?] [[? ?] ?]]. split;[|split].
      * split;[split|]; auto. unfold In in *. cbv in Hnumeq. cbv.
        erewrite Hnumeq. lia.
      * split;[split|]; auto. unfold In in *. cbv in Hnumeq. cbv.
        erewrite Hnumeq. lia.
      * split;[split|split;[split|]]; auto;
        (unfold In in *; cbv in Hnumeq; cbv; erewrite Hnumeq; lia).
  - apply ext_rel. split.
    + intros [? [? ?]]. auto.
    + intros [[? ?] [[? ?] ?]]. split;[|split].
      * split;[split|]; auto. unfold In in *. cbv in Hnumeq. cbv.
        erewrite Hnumeq. lia.
      * split;[split|]; auto. unfold In in *. cbv in Hnumeq. cbv.
        erewrite Hnumeq. lia.
      * split;[split|split;[split|]]; auto;
        (unfold In in *; cbv in Hnumeq; cbv; erewrite Hnumeq; lia).
  - apply ext_rel. split.
    + intros [? [? ?]]. auto.
    + intros [[? ?] [[? ?] ?]]. split;[|split].
      * split;[split|]; auto. unfold In in *. cbv in Hnumeq. cbv.
        erewrite Hnumeq. lia.
      * split;[split|]; auto. unfold In in *. cbv in Hnumeq. cbv.
        erewrite Hnumeq. lia.
      * split;[split|split;[split|]]; auto;
        (unfold In in *; cbv in Hnumeq; cbv; erewrite Hnumeq; lia).
  - apply ext_rel. split.
    + intros [? [? ?]]. auto.
    + intros [[? ?] [[? ?] ?]]. split;[|split].
      * split;[split|]; auto. unfold In in *. cbv in Hnumeq. cbv.
        erewrite Hnumeq. lia.
      * split;[split|]; auto. unfold In in *. cbv in Hnumeq. cbv.
        erewrite Hnumeq. lia.
      * split;[split|split;[split|]]; auto;
        (unfold In in *; cbv in Hnumeq; cbv; erewrite Hnumeq; lia).
Qed.

(** Bounding an execution already bounded with a greater bound is the same as
directly bounding the execution with the smaller bound *)

Lemma double_bounding_rew' (ex: Execution) (b1 b2: nat):
  valid_exec ex ->
  b1 < b2 ->
  bounded_exec (bounded_exec ex b2) b1 = bounded_exec ex b1.
Proof.
  intros Hval Hord.
  pose proof (bounded_exec_is_prefix _ b2 Hval) as Hpre2.
  pose proof (numbering_pre_stable _ _ Hpre2) as Hnumeq2.
  destruct ex. unfold bounded_exec. unfold bounded_exec in Hnumeq2.
  simpl. simpl in Hnumeq2. f_equal.
  - apply ext_set. split.
    + intros [? [? ?] ?]. split. auto.
      unfold In in *. erewrite Hnumeq2 in H1. lia.
    + intros [? ? ?]. split. 
      * split. auto. unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *.
        lia.
  - apply ext_rel. split.
    + intros [Hin1 [Hin2 [Hin3 [Hin4 Hrel]]]].
      split;[split|split;[split|]]. auto.
      * destruct Hin3; auto.
      * destruct Hin1 as [z Hin11 Hin12].
        cbv in Hin12. cbv in Hnumeq2. erewrite Hnumeq2 in Hin12.
        unfold In in *. lia.
      * destruct Hin4; auto.
      * destruct Hin2 as [z Hin21 Hin22].
        cbv in Hin22. cbv in Hnumeq2. erewrite Hnumeq2 in Hin22.
        unfold In in *. lia.
      * auto.
    + intros [[? ?] [[? ?] ?]].
      splitall; auto.
      * unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *. lia.
      * unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *. lia.
      * unfold In in *. lia.
      * unfold In in *. lia.
  - apply ext_rel. split.
    + intros [Hin1 [Hin2 [Hin3 [Hin4 Hrel]]]].
      split;[split|split;[split|]]. auto.
      * destruct Hin3; auto.
      * destruct Hin1 as [z Hin11 Hin12].
        cbv in Hin12. cbv in Hnumeq2. erewrite Hnumeq2 in Hin12.
        unfold In in *. lia.
      * destruct Hin4; auto.
      * destruct Hin2 as [z Hin21 Hin22].
        cbv in Hin22. cbv in Hnumeq2. erewrite Hnumeq2 in Hin22.
        unfold In in *. lia.
      * auto.
    + intros [[? ?] [[? ?] ?]].
      splitall; auto.
      * unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *. lia.
      * unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *. lia.
      * unfold In in *. lia.
      * unfold In in *. lia.
  - apply ext_rel. split.
    + intros [Hin1 [Hin2 [Hin3 [Hin4 Hrel]]]].
      split;[split|split;[split|]]. auto.
      * destruct Hin3; auto.
      * destruct Hin1 as [z Hin11 Hin12].
        cbv in Hin12. cbv in Hnumeq2. erewrite Hnumeq2 in Hin12.
        unfold In in *. lia.
      * destruct Hin4; auto.
      * destruct Hin2 as [z Hin21 Hin22].
        cbv in Hin22. cbv in Hnumeq2. erewrite Hnumeq2 in Hin22.
        unfold In in *. lia.
      * auto.
    + intros [[? ?] [[? ?] ?]].
      splitall; auto.
      * unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *. lia.
      * unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *. lia.
      * unfold In in *. lia.
      * unfold In in *. lia.
  - apply ext_rel. split.
    + intros [Hin1 [Hin2 [Hin3 [Hin4 Hrel]]]].
      split;[split|split;[split|]]. auto.
      * destruct Hin3; auto.
      * destruct Hin1 as [z Hin11 Hin12].
        cbv in Hin12. cbv in Hnumeq2. erewrite Hnumeq2 in Hin12.
        unfold In in *. lia.
      * destruct Hin4; auto.
      * destruct Hin2 as [z Hin21 Hin22].
        cbv in Hin22. cbv in Hnumeq2. erewrite Hnumeq2 in Hin22.
        unfold In in *. lia.
      * auto.
    + intros [[? ?] [[? ?] ?]].
      splitall; auto.
      * unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *. lia.
      * unfold In in *. lia.
      * cbv. cbv in Hnumeq2. erewrite Hnumeq2. unfold In in *. lia.
      * unfold In in *. lia.
      * unfold In in *. lia.
Qed.

(** If two events are conflicting in a bounded execution, they are also 
conflicting in the execution bounded by the greatest of the numberings of the
two events *)

Lemma bound_to_c_events (ex: Execution) (b:nat) (j k: Event):
  valid_exec ex ->
  numbering ex j <= numbering ex k ->
  numbering ex k < b ->
  c_events (bounded_exec ex b) j k ->
  c_events (bounded_exec ex (numbering ex k)) j k.
Proof.
  intros Hval Hord Hord' [Hmode [Hinj [Hink [Hjk Hkj]]]].
  repeat (apply conj).
  - auto.
  - destruct ex. simpl. destruct Hinj as [z Hjevts Hinj]. split.
    + simpl in Hjevts. auto.
    + unfold In. lia.
  - destruct ex. simpl. destruct Hink as [z Hkevts Hink]. split.
    + simpl in Hkevts. auto.
    + unfold In. lia.
  - intros Hnot. apply Hjk. 
    eapply sbrfsc_pre_inc. eapply bounded_exec_is_prefix.
    + eapply prefix_valid.
      * eapply prefix_valid. eauto. eapply bounded_exec_is_prefix. eauto.
      * eapply two_ord_bounds_pre. eauto.
    + erewrite double_bounding_rew'; eauto.
  - intros Hnot. apply Hkj. 
    eapply sbrfsc_pre_inc. eapply bounded_exec_is_prefix.
    + eapply prefix_valid.
      * eapply prefix_valid. eauto. eapply bounded_exec_is_prefix. eauto.
      * eapply two_ord_bounds_pre. eauto.
    + erewrite double_bounding_rew'; eauto.
Qed.

(** If two events are conflicting and if their numbering is strictly inferior to
a bound, this bound cannot be the smallest conflicting bounding *)

Lemma smallest_conflicting_bounding_conflict (ex: Execution) (j k: Event) (b: nat):
  valid_exec ex ->
  numbering ex k < b ->
  numbering ex j < b ->
  smallest_conflicting_bounding ex b ->
  c_events (bounded_exec ex b) j k ->
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
      rewrite c_events_sym. rewrite c_events_sym in Hconf.
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
  - destruct Hconf as [_ [_ [? _]]]. destruct ex. simpl in H.
    destruct H as [? ?]. unfold In in *. lia.
  - destruct (Compare_dec.lt_eq_lt_dec (numbering ex j) (numbering ex k)) as [[Hjlt|Hjeq]|Hjgt].
    + rewrite (max_rewrite _ _ Hjlt). auto.
    + rewrite Hjeq, PeanoNat.Nat.max_id. auto.
    + destruct Hconf as [_ [H _]].
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
      * destruct Hconf as [_ [? _]]. destruct ex. simpl in H.
        destruct H as [? ?]. unfold In in *. lia.
Qed. 

  
End NumberingPrefix.
