(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Relations.
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

Definition c_events (e: Execution) : relation Event :=
  fun x => fun y =>
    ((get_mode x) <> Sc \/
     (get_mode y) <> Sc) /\
    ~ (((sb e) <+> (res_mode Sc (rf e)))⁺) x y /\
    ~ (((sb e) <+> (res_mode Sc (rf e)))⁺) y x.

(** * SC-consistent prefixes *)

Lemma nt_rfsc_incl_hb: forall ex,
  valid_exec ex ->
  (res_mode Sc (rf ex)) ⊆  ((sb ex) <+> (sw ex)).
Proof.
  intros ex Hval x y H.
  right. exists x; split.
  { apply (e_seqmode_refl x (res_mode_fst_mode H)).
    unfold stronger_or_eq_mode. auto. }
    exists x; split.
    { right. }
    exists x; split.
    { exists x; split.
    { destruct H as [z [[Heq Hmode] [z' [Hrf Heq']]]].
      rewrite <- Heq in Hrf.
      repeat (try split); apply (rf_orig_write x z' Hval Hrf). }
      exists x; split.
      { right. }
      exists x; split.
      { destruct H as [z [[Heq Hmode] [z' [Hrf Heq']]]].
      rewrite <- Heq in Hrf.
      exists x; split.
      - repeat (try split); apply (rf_orig_write x z' Hval Hrf).
      - repeat (try split). unfold stronger_or_eq_mode. rewrite Hmode. auto.
      }
      apply rt_refl.
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
    { right. }
    { split; auto.
      destruct H as [z [_ [z' [_ [Heq Hmode]]]]].
      rewrite Heq in Hmode. rewrite Hmode.
      unfold stronger_or_eq_mode. auto.
    }
Qed.

Lemma sbrfsc_incl_hb: forall ex,
  valid_exec ex ->
  (((sb ex) <+> (res_mode Sc (rf ex)))⁺) ⊆ (hb ex).
Proof.
  intros ex Hval x y H. induction H as [|z1 z2 z3 H IH H' IH'].
  - left. destruct H as [H|H].
    + left. auto.
    + apply (nt_rfsc_incl_hb ex Hval). auto.
  - right with (y := z2).
    + apply IH.
    + apply IH'.
Qed.

Lemma rf_prefix_in_sbrfsc_ex: forall pre ex,
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  (forall x y, ~ (c_events pre) x y) ->
  (rf pre) ⊆ (((sb ex) <+> ((res_mode Sc (rf ex))))⁺).
Proof.
  intros pre ex Hval H11cons Hpre Hnoconflict x y H.
  (* We suppose that x and y are related by ex.rf *)
  apply (rf_prefix_incl Hpre) in H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { left. right. 
    exists x; split. { split; auto. }
    exists y; split. { auto. }
    split; auto. }
  destruct (classic ((((sb ex) <+> (res_mode Sc (rf ex))) ⁺) x y)) 
    as [Hres | Hcontr].
  { auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)⁺ *)
  exfalso.
  destruct (classic ((((sb ex) <+> (res_mode Sc (rf ex))) ⁺) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)⁺ *)
  - destruct H11cons as [Hco _].
    apply (sbrfsc_incl_hb ex Hval) in Hres'.
    destruct (coherence_no_future_read Hco) with (x := x).
    exists y; split; auto.
  (* If y and x are not related by ex.(sb U rf_sc)⁺ *)
  - apply not_and_or in HNotSc. apply (Hnoconflict x y).
    repeat (try split).
    + auto.
    + intros Hcontr''.
      assert ((((sb pre) <+> (res_mode Sc (rf pre))) ⁺) ⊆
              (((sb ex) <+> (res_mode Sc (rf ex))) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert ((((sb pre) <+> (res_mode Sc (rf pre))) ⁺) ⊆
                       (((sb ex) <+> (res_mode Sc (rf ex))) ⁺)) as Hincl.
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
  (mo pre) ⊆ ((((sb ex) <+> ((res_mode Sc (rf ex))))⁺) <+> 
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
  destruct (classic ((((sb ex) <+> (res_mode Sc (rf ex))) ⁺) x y)) 
    as [Hres | Hcontr].
  { left. auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)⁺ *)
  exfalso.
  destruct (classic ((((sb ex) <+> (res_mode Sc (rf ex))) ⁺) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)⁺ *)
  - destruct H11cons as [Hco _].
    apply (sbrfsc_incl_hb ex Hval) in Hres'.
    destruct (coherence_coherence_ww Hco) with (x := x).
    exists y; split; auto.
  (* If y and x are not related by ex.(sb U rf_sc)⁺ *)
  - apply not_and_or in HNotSc. apply (Hnoconflict x y).
    repeat (try split).
    + auto.
    + intros Hcontr''.
      assert ((((sb pre) <+> (res_mode Sc (rf pre))) ⁺) ⊆
              (((sb ex) <+> (res_mode Sc (rf ex))) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert ((((sb pre) <+> (res_mode Sc (rf pre))) ⁺) ⊆
              (((sb ex) <+> (res_mode Sc (rf ex))) ⁺)) as Hincl.
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
  (rb pre) ⊆ ((((sb ex) <+> ((res_mode Sc (rf ex))))⁺) <+>
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
  destruct (classic ((((sb ex) <+> (res_mode Sc (rf ex))) ⁺) x y)) 
    as [Hres | Hcontr].
  { left. auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)⁺ *)
  exfalso.
  destruct (classic ((((sb ex) <+> (res_mode Sc (rf ex))) ⁺) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)⁺ *)
  - destruct H11cons as [Hco _].
    apply (sbrfsc_incl_hb ex Hval) in Hres'.
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
      assert ((((sb pre) <+> (res_mode Sc (rf pre))) ⁺) ⊆
              (((sb ex) <+> (res_mode Sc (rf ex))) ⁺)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists x'; split. { split; auto. }
          exists y'; split. { apply (rf_prefix_incl Hpre). auto. }
          split; auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert ((((sb pre) <+> (res_mode Sc (rf pre))) ⁺) ⊆
              (((sb ex) <+> (res_mode Sc (rf ex))) ⁺)) as Hincl.
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


Lemma sb_sc_eco_sc_incl_psc : forall ex,
  valid_exec ex ->
  ((res_mode Sc (sb ex)) <+> (res_mode Sc (rf ex)) <+> (res_mode Sc (mo ex)) <+>
  (res_mode Sc (rb ex))) ⊆ (psc ex).
Proof.
  intros ex Hval x y H.
  destruct H as [Hsb | [Hrf | [Hmo | Hrb]]]; left.
  - exists x; split.
    { left. split; auto. apply (res_mode_fst_mode Hsb). }
    exists y; split.
    { left. apply (res_mode_rel Hsb). }
    { left. split; auto. apply (res_mode_snd_mode Hsb). }
  - exists x; split.
    { left. split; auto. apply (res_mode_fst_mode Hrf). }
    exists y; split.
    { right; right; left. split.
      - apply tc_incl_itself. apply (nt_rfsc_incl_hb ex Hval). auto.
      - apply res_mode_rel in Hrf. apply (rf_same_loc x y Hval Hrf).
    }
    left. split; auto. apply (res_mode_snd_mode Hrf).
  - exists x; split.
    { left. split; auto. apply (res_mode_fst_mode Hmo). }
    exists y; split.
    { right; right; right; left.
      apply (res_mode_rel Hmo). }
    { left. split; auto. apply (res_mode_snd_mode Hmo). }
  - exists x; split.
    { left. split; auto. apply (res_mode_fst_mode Hrb). }
    exists y; split.
    { right; right; right; right.
      apply (res_mode_rel Hrb). }
    { left. split; auto. apply (res_mode_snd_mode Hrb). }
Qed.
  

Lemma sb_sc_eco_sc_ac_impl_sb_eco_sc_ac: forall ex,
  acyclic ((res_mode Sc (sb ex)) <+> (res_mode Sc (rf ex)) <+> 
           (res_mode Sc (mo ex)) <+> (res_mode Sc (rb ex))) ->
  acyclic ((sb ex) <+> (res_mode Sc (rf ex)) <+> (res_mode Sc (mo ex)) <+>
           (res_mode Sc (rb ex))).
Proof.
  admit.
Admitted.

Lemma sb_eco_sc_acyclic: forall ex,
  rc11_consistent ex ->
  acyclic ((sb ex) <+> (res_mode Sc (eco ex))).
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
  - admit.
Admitted.