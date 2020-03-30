(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.
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

Lemma mcp_bound_min_one_lt_bound (ex: Execution) (bound: nat) (k j: Event):
  minimal_conflicting_pair ex bound k j ->
  bound - 1 < bound.
Proof.
  intros Hmcp.
  assert (bound > 0). eauto using mcp_bound_gt_zero.
  lia.
Qed.

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

Lemma sbrf_boundable (ex: Execution) (b: nat):
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

Lemma sbbefore_lemma (ex: Execution) (bound: nat) (x y: Event):
  valid_exec ex ->
  rc11_consistent ex ->
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) > (numbering ex y) ->
  (forall b, (sb ex) b y ->
             ~((sb ex ⊔ rf ex)^+ x b)).
Proof.
  intros Hval Hrc11 Hmcp Hord b Hsb.
  eapply mcp_not_sbrfsc in Hmcp as Hnotsbrfsc.
  intros Hnot; apply Hnotsbrfsc.
  apply tc_trans with b.
  - assert (bound >= numbering ex b) as Hordbndb.
    { transitivity (numbering ex y).
      - eauto using mcp_right_le_bound.
      - eauto using sb_num_ord. }
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
      rewrite (max_rewrite' _ _ Hord) in Hmcp.
      rewrite Hmcp in Hord. apply sb_num_ord in Hsb. lia.
  - apply tc_incl_itself. left. rew bounded.
    exists y. exists b.
    + split; auto. apply sb_num_ord in Hsb. unfold NLE.
      apply mcp_right_le_bound in Hmcp. lia.
    + auto.
    + split; auto. apply mcp_right_le_bound in Hmcp. unfold NLE. lia.
Qed.

Lemma mcp_write_race (ex: Execution) (bound: nat) (x y: Event):
  minimal_conflicting_pair ex bound x y ->
  (numbering ex x) > (numbering ex y) ->
  is_write x ->
  race (bounded_exec ex bound) x y.
Proof.
  intros Hmcp Hord Hw.
  repeat (apply conj).
  - eauto using mcp_one_is_write.
  - eauto using mcp_diff.
  - eauto using mcp_same_loc.
  - admit.
  - admit.
Admitted.

End DRF.