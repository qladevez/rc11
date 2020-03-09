(* 
This project is an attempt at formalising the proof of DRF-SC for the repaired 
C11 memory model presented in the article (Repairing Sequential Consistency in 
C/C++11; Lahav, Vafeiadis, Kang et al., PLDI 2017)

Author: Quentin Ladeveze, Inria Paris, France
*)

From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.
Require Import Ensembles.
Require Import Relations.
Require Import Classical_Prop.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import rc11.
From RC11 Require Import prefix.

(** This file contains the definition of the pairs of conflicting events and
some properties about executions that contain (or don't contain) conflicting
events *)

(** * Conflicts *)

(** ** Conflicting events *)

Definition c_events (e: Execution) : relation Event :=
  fun x => fun y =>
    ((get_mode x) <> Sc \/
     (get_mode y) <> Sc) /\
    ~ (((sb e) ⊔ (res_mode Sc (rf e)))^+) x y /\
    ~ (((sb e) ⊔ (res_mode Sc (rf e)))^+) y x.


Definition not_conflicting (ex: Execution) : Prop :=
  forall x y, ~(c_events ex) x y.

Definition conflicting (ex: Execution) : Prop :=
  exists x y, (c_events ex) x y.

Lemma not_no_conflict_is_exist_conflict (ex: Execution):
  ~(not_conflicting ex) <-> (conflicting ex).
Proof.
  split; intros H.
  - byabsurd. destruct H. intros x y H.
    apply Hcontr. exists x, y. auto.
  - intros Hcontr. destruct H as [x [y H]].
    destruct (Hcontr _ _ H).
Qed.

Lemma not_exists_conflict_is_no_conflict (ex: Execution):
  ~(conflicting ex) <-> (not_conflicting ex).
Proof.
  split; intros H.
  - intros x y Hcontr. apply H. exists x,y; auto.
  - intros [x [y Hcontr]].
    destruct (H _ _ Hcontr).
Qed.

Ltac solve_test_ineq :=
  unfold inj; simpl;
  intros x y [Heq Hmode]; split; auto;
  unfold Mse; unfold M in Hmode;
  destruct (get_mode x); simpl in *;
  intuition eauto.
  
(** ** SC-consistent prefixes *)

Lemma nt_rfsc_incl_hb {ex: Execution}:
  valid_exec ex ->
  [M Sc] ⋅ rf ex ⋅ [M Sc] ≦  sw ex.
Proof.
  intros Hval.
  unfold sw.
  rewrite <- !one_incl_refl, !dotx1.
  apply incl_dot_test_right.
  solve_test_ineq.
  apply incl_dot_test_right.
  solve_test_ineq.
  rewrite <- !dotA.
  apply incl_dot_test_left.
  solve_test_ineq.
  rewrite !dotA.
  unfold rs.
  rewrite <- one_incl_refl, <- one_incl_rtc, !dotx1, dtest.
  rewrite (rf_wr _ Hval) at 1.
  mrewrite (test_dot_comm _ R).
  apply incl_dot_test_right. auto.
  rewrite (test_in_one _ (M Sc)) at 2.
  rewrite (test_in_one _ R).
  rewrite !dotx1.
  apply incl_dot; auto.
  rewrite test_dot_comm.
  apply incl_dot; auto.
  solve_test_ineq.
Qed.

Lemma sbrfsc_incl_hb {ex: Execution}:
  valid_exec ex ->
  (sb ex ⊔ ([M Sc] ⋅ rf ex ⋅ [M Sc]))^+ ≦ hb ex.
Proof.
  intros Hval.
  unfold hb.
  apply tc_incl.
  apply incl_cup; auto.
  apply (nt_rfsc_incl_hb Hval).
Qed.

Lemma rf_prefix_in_sbrfsc_ex {pre ex: Execution}:
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  not_conflicting pre ->
  (rf pre) ≦ (((sb ex) ⊔ ((res_mode Sc (rf ex))))^+).
Proof.
  intros Hval H11cons Hpre Hnoconflict x y H.
  (* We suppose that x and y are related by ex.rf *)
  apply (rf_prefix_incl Hpre) in H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { apply tc_incl_itself. right. 
    exists y. exists x.
    - apply M_get_mode_refl; auto.
    - auto.
    - apply M_get_mode_refl; auto.
  }
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) x y)) 
    as [Hres | Hcontr].
  { auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)^+ *)
  exfalso.
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)^+ *)
  - destruct H11cons as [Hco _].
    apply (sbrfsc_incl_hb  Hval) in Hres'.
    destruct (coherence_no_future_read _ Hco) with (x := x).
    exists y; auto.
  (* If y and x are not related by ex.(sb U rf_sc)^+ *)
  - apply not_and_or in HNotSc. apply (Hnoconflict x y).
    repeat (try split).
    + auto.
    + intros Hcontr''.
      assert ((((sb pre) ⊔ (res_mode Sc (rf pre))) ^+) ≦
              (((sb ex) ⊔ (res_mode Sc (rf ex))) ^+)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists y'; [exists x'|];
          try (apply M_get_mode_refl; auto).
          apply (rf_prefix_incl Hpre). auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert ((((sb pre) ⊔ (res_mode Sc (rf pre))) ^+) ≦
                       (((sb ex) ⊔ (res_mode Sc (rf ex))) ^+)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists y'; [exists x'|];
          try (apply M_get_mode_refl; auto).
          apply (rf_prefix_incl Hpre). auto. }
      apply Hincl in Hcontr''. eauto.
Qed.

(** When the prefix of an execution doesn't contain any conflicting events, the
modification order of the prefix is included in the union of transitive closure 
of the union of the sequenced-before the reads-from restricted to SC events 
relations of this execution and of the modification order restricted to SC events
of this execution *)

Lemma mo_prefix_in_sbrfscmo_ex {pre ex: Execution}:
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  not_conflicting pre ->
  (mo pre) ≦ ((((sb ex) ⊔ ((res_mode Sc (rf ex))))^+) ⊔ 
                               (res_mode Sc (mo ex))).
Proof.
  intros Hval H11cons Hpre Hnoconflict x y H.
  (* We suppose that x and y are related by ex.rf *)
  apply (mo_prefix_incl Hpre) in H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { right. 
    exists y. exists x.
    - apply M_get_mode_refl; auto.
    - auto.
    - apply M_get_mode_refl; auto.
  }
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) x y)) 
    as [Hres | Hcontr].
  { left. auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)^+ *)
  exfalso.
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)^+ *)
  - destruct H11cons as [Hco _].
    apply (sbrfsc_incl_hb  Hval) in Hres'.
    destruct (coherence_coherence_ww _ Hco) with (x := x).
    exists y; auto.
  (* If y and x are not related by ex.(sb U rf_sc)^+ *)
  - apply not_and_or in HNotSc. apply (Hnoconflict x y).
    repeat (try split).
    + auto.
    + intros Hcontr''.
      assert ((((sb pre) ⊔ (res_mode Sc (rf pre))) ^+) ≦
              (((sb ex) ⊔ (res_mode Sc (rf ex))) ^+)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists y'; [exists x'|];
          try (apply M_get_mode_refl; auto).
          apply (rf_prefix_incl Hpre). auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert ((((sb pre) ⊔ (res_mode Sc (rf pre))) ^+) ≦
                       (((sb ex) ⊔ (res_mode Sc (rf ex))) ^+)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists y'; [exists x'|];
          try (apply M_get_mode_refl; auto).
          apply (rf_prefix_incl Hpre). auto. }
      apply Hincl in Hcontr''. eauto.
Qed.

(** When the prefix of an execution doesn't contain any conflicting events, the
reads-before relation of the prefix is included in the union of transitive 
closure of the union of the sequenced-before the reads-from restricted to SC 
events relations of this execution and of the modification order restricted to 
SC events of this execution *)

Lemma rb_prefix_in_sbrfscrb_ex {pre ex: Execution}:
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  not_conflicting pre ->
  (rb pre) ≦ ((((sb ex) ⊔ ((res_mode Sc (rf ex))))^+) ⊔
                               (res_mode Sc (rb ex))).
Proof.
  intros Hval H11cons Hpre Hnoconflict x y H.
  (* We suppose that x and y are related by ex.rf *)
  apply (rb_prefix_incl Hpre) in H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { right. 
    exists y. exists x.
    - apply M_get_mode_refl; auto.
    - auto.
    - apply M_get_mode_refl; auto.
  }
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) x y)) 
    as [Hres | Hcontr].
  { left. auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)^+ *)
  exfalso.
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)^+ *)
  - destruct H11cons as [Hco _].
    apply (sbrfsc_incl_hb  Hval) in Hres'.
    destruct H as [z Hrfinv Hmo].    
    destruct (coherence_coherence_wr _ Hco) with (x := z).
    exists x. exists y; auto. auto.
  (* If y and x are not related by ex.(sb U rf_sc)^+ *)
  - apply not_and_or in HNotSc. apply (Hnoconflict x y).
    repeat (try split).
    + auto.
    + intros Hcontr''.
      assert ((((sb pre) ⊔ (res_mode Sc (rf pre))) ^+) ≦
              (((sb ex) ⊔ (res_mode Sc (rf ex))) ^+)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists y'; [exists x'|];
          try (apply M_get_mode_refl; auto).
          apply (rf_prefix_incl Hpre). auto. }
      apply Hincl in Hcontr''. eauto.
    + intros Hcontr''.
      assert ((((sb pre) ⊔ (res_mode Sc (rf pre))) ^+) ≦
                       (((sb ex) ⊔ (res_mode Sc (rf ex))) ^+)) as Hincl.
      { apply tc_incl. intros x' y' H'. destruct H' as [H'|H'].
        - left. apply (sb_prefix_incl Hpre). auto.
        - destruct (res_mode_simp H') as [Hsc [Hsc' Hrf]].
          right. exists y'; [exists x'|];
          try (apply M_get_mode_refl; auto).
          apply (rf_prefix_incl Hpre). auto. }
      apply Hincl in Hcontr''. eauto.
Qed.

(** In a rc11-consistent execution, the union of the sequenced-before relation
and of the extended communication relation restricted to pairs of SC events is
acyclic *)

Lemma sb_sc_eco_sc_incl_psc {ex: Execution}:
  valid_exec ex ->
  ((res_mode Sc (sb ex)) ⊔ (res_mode Sc (rf ex)) ⊔ (res_mode Sc (mo ex)) ⊔
  (res_mode Sc (rb ex))) ≦ (psc ex).
Proof.
  intros Hval.
  apply union_incl; [apply union_incl; [apply union_incl|]|];
  unfold psc; apply incl_union_left; unfold psc_base;
  rewrite <- union_seq_left; rewrite <- seq_union_left;
  unfold scb.
  - apply incl_dot; [apply incl_dot|]; auto. kat.
  - apply incl_dot_test_right. auto.
    rewrite <- !dotA. apply incl_dot_test_left. auto.
    rewrite -> !dotA.
    apply incl_union_left. apply incl_union_left. apply incl_union_right.
    apply (rf_incl_same_loc (evts ex) _ ).
    + destruct_val_exec Hval. apply rf_valid_test_right, rf_valid_test_left.
      auto.
    + unfold hb.
      rewrite tc_incl_itself. apply tc_incl.
      apply incl_union_right. apply (nt_rfsc_incl_hb Hval).
  - apply incl_dot; [apply incl_dot|]; auto. kat.
  - apply incl_dot; [apply incl_dot|]; auto. kat.
Qed.

Lemma sb_sc_eco_sc_ac_impl_sb_eco_sc_ac ex:
  valid_exec ex ->
  acyclic ((res_mode Sc (sb ex)) ⊔ 
           (res_mode Sc (rf ex)) ⊔ 
           (res_mode Sc (mo ex)) ⊔
           (res_mode Sc (rb ex))) ->
  acyclic ((sb ex) ⊔ 
           (res_mode Sc (rf ex)) ⊔ 
           (res_mode Sc (mo ex)) ⊔
           (res_mode Sc (rb ex))).
Proof.
  intros Hval H.
  byabsurd.
  rewrite (dcmp_in_res_neq_res Sc (sb ex)) in Hcontr.
  rewrite <- union_assoc in Hcontr.
  assert (acyclic (res_neq_mode Sc (sb ex))) as Hprob.
  { destruct_val_exec Hval. destruct Hsb_v as [Hlin _].
    apply lin_strict_ac in Hlin.
    apply ac_incl with (r1 := (res_neq_mode Sc (sb ex))) in Hlin.
    - auto.
    - apply res_neq_incl. }
  apply not_acyclic_is_cyclic in Hcontr.
  destruct Hcontr as [w Hcontr].
  apply (ac_union w) with (r1 := (res_mode Sc (rf ex) ⊔ res_mode Sc (mo ex) ⊔ res_mode Sc (rb ex)) ⊔ res_mode Sc (sb ex)) in Hprob.
  - admit.
  - admit.
  - rewrite <- union_assoc. rewrite union_comm in Hcontr.
    rewrite <- union_assoc in Hcontr. rewrite union_comm in Hcontr.
    rewrite (union_comm (res_mode Sc (sb ex)) _). 
    rewrite <- union_assoc in Hcontr. rewrite <- union_assoc in Hcontr.
    rewrite <- union_assoc. rewrite <- union_assoc. auto.
    rewrite <- union_assoc in Hcontr. auto.
Admitted.

Lemma sb_eco_sc_acyclic ex:
  valid_exec ex ->
  rc11_consistent ex ->
  acyclic ((sb ex) ⊔ 
           (res_mode Sc (rf ex)) ⊔ 
           (res_mode Sc (mo ex)) ⊔
           (res_mode Sc (rb ex))).
Proof.
  intros Hval Hrc11.
  apply sb_sc_eco_sc_ac_impl_sb_eco_sc_ac.
  - apply Hval.
  - destruct Hrc11 as [_ [_ [Hsc _]]].
    apply (ac_incl _ _ Hsc).
    apply (sb_sc_eco_sc_incl_psc Hval).
Qed.

(** If the prefix of an RC11-concistent execution doesn't contain any pair of 
conflicting events, it is SC-consistent *)

Lemma no_conflict_prefix_sc : forall pre ex,
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  not_conflicting pre ->
  sc_consistent pre.
Proof.
  intros pre ex Hval Hrc11 Hpre Hconflict.
  split.
  - destruct (prefix_rc11_consistent Hrc11 Hpre) as [_ [Hat _]].
    auto.
  - apply (ac_incl _ _ (tc_ac_is_ac _ (sb_eco_sc_acyclic _ Hval Hrc11))).
    apply union_incl; [apply union_incl; [apply union_incl|]|].
    + apply (incl_trans2 _ _ _ (tc_incl_itself _)).
      incl_union_r; incl_union_r; incl_union_r.
      apply (sb_prefix_incl Hpre).
    + repeat (rewrite -> union_assoc);
      apply (incl_trans2 _ _ _ (incl_tc_union _ _)); incl_union_r.
      repeat (rewrite -> union_assoc);
      apply (incl_trans2 _ _ _ (incl_tc_union _ _)); incl_union_r.
      apply (rf_prefix_in_sbrfsc_ex Hval Hrc11 Hpre Hconflict).
    + repeat (rewrite -> union_assoc);
      apply (incl_trans2 _ _ _ (incl_tc_union _ _)); incl_union_r.
      rewrite -> union_assoc;
      apply (incl_trans2 _ _ _ (incl_tc_union _ _)).
      apply (incl_trans2 _ _ _ (incl_union_of_tc_right _ _)).
      apply (mo_prefix_in_sbrfscmo_ex Hval Hrc11 Hpre Hconflict).
    + repeat (rewrite <- union_assoc).
      rewrite (union_comm (res_mode _ (mo _)) _).
      repeat (rewrite union_assoc).
      apply (incl_trans2 _ _ _ (incl_tc_union _ _)); incl_union_r.
      rewrite -> union_assoc;
      apply (incl_trans2 _ _ _ (incl_tc_union _ _)).
      apply (incl_trans2 _ _ _ (incl_union_of_tc_right _ _)).
      apply (rb_prefix_in_sbrfscrb_ex Hval Hrc11 Hpre Hconflict).
Qed.

(** If an execution is not SC-consistent, it contains (a) pair(s) of conflicting
event(s) *)

Theorem exec_sc_no_conflict (ex: Execution) :
  valid_exec ex ->
  rc11_consistent ex ->
  ~(sc_consistent ex) ->
  conflicting ex.
Proof.
  intros Hval Hrc11 Hsc. apply not_no_conflict_is_exist_conflict. 
  intros Hconf. apply Hsc.
  apply (no_conflict_prefix_sc ex ex); auto.
  apply prefix_itself. apply Hval.
Qed.
