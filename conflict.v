(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Classical_Prop.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import rc11.
From RC11 Require Import prefix.

Import RelNotations.

(** This file contains the definition of the pairs of conflicting events and
some properties about executions that contain (or don't contain) conflicting
events *)

Check res_mode.

(** * Conflicting events *)

Definition c_events (e: Execution) : Rln Event :=
  fun x => fun y =>
    ((get_mode x) <> Sc \/
     (get_mode y) <> Sc) /\
    ~ (rel_union (sb e) (res_mode Sc (rf e))⁺) x y /\
    ~ (rel_union (sb e) (res_mode Sc (rf e))⁺) y x.

(** * SC-consistent prefixes *)

Lemma hb_incl_sbrfsc: forall ex,
  valid_exec ex ->
  rel_incl (rel_union (sb ex) (res_mode Sc (rf ex))⁺) (hb ex).
Proof.
  intros ex Hval x y H. induction H as [|z1 z2 z3 H IH H' IH'].
  - apply trc_step. destruct H as [H|H].
    + left. auto.
    + right. exists x; split.
      { destruct H as [z [[Heq Hmode] _]].
        split; auto. rewrite Hmode.
        unfold stronger_or_eq_mode. auto. }
      exists x; split.
      { right. auto. }
      exists x; split.
      { exists x; split.
        { destruct H as [z [[Heq Hmode] [z' [Hrf Heq']]]].
          rewrite <- Heq in Hrf.
          repeat (try split); apply (rf_orig_write x z' Hval Hrf). }
        exists x; split.
        { right. auto. }
        exists x; split.
        { destruct H as [z [[Heq Hmode] [z' [Hrf Heq']]]].
          rewrite <- Heq in Hrf.
          exists x; split.
          - repeat (try split); apply (rf_orig_write x z' Hval Hrf).
          - repeat (try split). unfold stronger_or_eq_mode. rewrite Hmode. auto.
        }
        apply trc_step. right. auto.
      }
      exists y; split.
      { destruct H as [z [[Heq Hmode] [z' [Hrf [Heq' Hmode']]]]].
        rewrite <- Heq in Hrf. rewrite Heq' in Hrf. auto. }
      exists y; split.
      { destruct H as [z [[Heq Hmode] [z' [Hrf [Heq' Hmode']]]]].
        rewrite <- Heq in Hrf. rewrite Heq' in Hrf.
        exists y; split.
        - repeat (try split); apply (rf_dest_read x y Hval Hrf).
        - split; auto. unfold stronger_or_eq_mode. rewrite Heq' in Hmode'.
          rewrite Hmode'. auto.
      }
      exists y; split.
      { right. auto. }
      { split; auto.
        destruct H as [z [_ [z' [_ [Heq Hmode]]]]].
        rewrite Heq in Hmode. rewrite Hmode.
        unfold stronger_or_eq_mode. auto.
      }
  - apply trc_ind with (z := z3).
    + apply IH.
    + apply IH'.
Qed.

Lemma rf_prefix_in_sbrfsc_ex: forall pre ex,
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  (forall x y, ~ (c_events pre) x y) ->
  rel_incl (rf pre) (rel_union (sb ex) ((res_mode Sc (rf ex)))⁺).
Proof.
  intros pre ex Hval H11cons Hpre Hnoconflict x y H.
  (* We suppose that x and y are related by ex.rf *)
  apply (rf_prefix_incl Hpre) in H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { apply trc_step. right. 
    exists x; split. { split; auto. }
    exists y; split. { auto. }
    split; auto. }
  destruct (classic ((rel_union (sb ex) (res_mode Sc (rf ex)) ⁺) x y)) 
    as [Hres | Hcontr].
  { auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)⁺ *)
  exfalso.
  destruct (classic ((rel_union (sb ex) (res_mode Sc (rf ex)) ⁺) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)⁺ *)
  - destruct H11cons as [Hco _].
    apply (hb_incl_sbrfsc ex Hval) in Hres'.
    destruct (coherence_no_future_read Hco) with (x := x).
    exists y; split; auto.
  (* If y and x are not related by ex.(sb U rf_sc)⁺ *)
  - apply not_and_or in HNotSc. apply (Hnoconflict x y).
    repeat (try split).
    + auto.
    + intros Hcontr''.
      assert (rel_incl (rel_union (sb pre) (res_mode Sc (rf pre)) ⁺)
                       (rel_union (sb ex) (res_mode Sc (rf ex)) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert (rel_incl (rel_union (sb pre) (res_mode Sc (rf pre)) ⁺)
                       (rel_union (sb ex) (res_mode Sc (rf ex)) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
Qed.

(** When the prefix of an execution doesn't contain any conflicting events, the
modification order of the prefix is included in the union of transitive closure 
of the union of the sequenced-before the reads-from restricted to SC events 
relations of this execution and of the modification order restricted to SC events
of this execution *)

Lemma mo_prefix_in_sbrfscmo_ex: forall pre ex,
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  (forall x y, ~ (c_events pre) x y) ->
  rel_incl (mo pre) (rel_union (rel_union (sb ex) ((res_mode Sc (rf ex)))⁺) 
                               (res_mode Sc (mo ex))).
Proof.
  intros pre ex Hval H11cons Hpre Hnoconflict x y H.
  (* We suppose that x and y are related by ex.mo *)
  apply (mo_prefix_incl Hpre) in H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { right. 
    exists x; split. { split; auto. }
    exists y; split. { auto. }
    split; auto. }
  destruct (classic ((rel_union (sb ex) (res_mode Sc (rf ex)) ⁺) x y)) 
    as [Hres | Hcontr].
  { left. auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)⁺ *)
  exfalso.
  destruct (classic ((rel_union (sb ex) (res_mode Sc (rf ex)) ⁺) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)⁺ *)
  - destruct H11cons as [Hco _].
    apply (hb_incl_sbrfsc ex Hval) in Hres'.
    destruct (coherence_coherence_ww Hco) with (x := x).
    exists y; split; auto.
  (* If y and x are not related by ex.(sb U rf_sc)⁺ *)
  - apply not_and_or in HNotSc. apply (Hnoconflict x y).
    repeat (try split).
    + auto.
    + intros Hcontr''.
      assert (rel_incl (rel_union (sb pre) (res_mode Sc (rf pre)) ⁺)
                       (rel_union (sb ex) (res_mode Sc (rf ex)) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert (rel_incl (rel_union (sb pre) (res_mode Sc (rf pre)) ⁺)
                       (rel_union (sb ex) (res_mode Sc (rf ex)) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
Qed.

(** When the prefix of an execution doesn't contain any conflicting events, the
reads-before relation of the prefix is included in the union of transitive 
closure of the union of the sequenced-before the reads-from restricted to SC 
events relations of this execution and of the modification order restricted to 
SC events of this execution *)

Lemma rb_prefix_in_sbrfscmo_ex: forall pre ex,
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  (forall x y, ~ (c_events pre) x y) ->
  rel_incl (rb pre) (rel_union (rel_union (sb ex) ((res_mode Sc (rf ex)))⁺) 
                               (res_mode Sc (rb ex))).
Proof.
  intros pre ex Hval H11cons Hpre Hnoconflict x y H.
  (* We suppose that x and y are related by ex.mo *)
  apply (rb_prefix_incl Hpre) in H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { right. 
    exists x; split. { split; auto. }
    exists y; split. { auto. }
    split; auto. }
  destruct (classic ((rel_union (sb ex) (res_mode Sc (rf ex)) ⁺) x y)) 
    as [Hres | Hcontr].
  { left. auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)⁺ *)
  exfalso.
  destruct (classic ((rel_union (sb ex) (res_mode Sc (rf ex)) ⁺) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)⁺ *)
  - destruct H11cons as [Hco _].
    apply (hb_incl_sbrfsc ex Hval) in Hres'.
    destruct H as [z [H1 H2]].
    destruct (coherence_coherence_wr Hco) with (x := z).
    exists y; split.
    + auto.
    + exists x; split; auto.
  (* If y and x are not related by ex.(sb U rf_sc)⁺ *)
  - apply not_and_or in HNotSc. apply (Hnoconflict x y).
    repeat (try split).
    + auto.
    + intros Hcontr''.
      assert (rel_incl (rel_union (sb pre) (res_mode Sc (rf pre)) ⁺)
                       (rel_union (sb ex) (res_mode Sc (rf ex)) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert (rel_incl (rel_union (sb pre) (res_mode Sc (rf pre)) ⁺)
                       (rel_union (sb ex) (res_mode Sc (rf ex)) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
Qed.

(** In a rc11-consistent execution, the union of the sequenced-before relation
and of the extended communication relation restricted to pairs of SC events is
acyclic *)

Lemma sb_eco_sc_incl_psc : forall ex,
  rel_incl (res_mode Sc (rel_union (sb ex) (eco ex))) (psc ex).
Proof.
  intros ex x y H.
  destruct H as [z [[Heq Hsc] [z' [H [Heq' Hsc']]]]].
  rewrite <- Heq in H; rewrite Heq' in H.
  destruct H as [H | H].
  { left. exists x; split.
    { left. split; auto. }
    exists y; split.
    { left. auto. }
    left; split; auto. rewrite <- Heq'. auto.
  }
  induction H.
  - destruct H as [H | [H | H]].
    + 
Admitted.

Lemma sb_eco_sc_acyclic: forall ex,
  rc11_consistent ex ->
  acyclic (rel_union (sb ex) (res_mode Sc (eco ex))).
Proof.
Admitted.

(** If the prefix of an RC11-concistent execution doesn't contain any pair of 
conflicting events, it is SC-consistent *)

Lemma no_conflict_prefix_sc : forall pre ex,
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  (forall x y, ~ (c_events pre) x y) ->
  sc_consistent pre.
Proof.
  intros pre ex Hval Hrc11 Hpre Hconflict.
  split.
  - destruct (prefix_rc11_consistent Hrc11 Hpre) as [_ [Hat _]].
    auto.
  - destruct Hrc11 as [