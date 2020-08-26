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
From RC11 Require Import proprel_classic.
From RC11 Require Import util.
From RC11 Require Import exec.
From RC11 Require Import rc11.
From RC11 Require Import prefix.

(** This file contains the definition of the pairs of conflicting events and
some properties about executions that contain (or don't contain) conflicting
events *)

(** * Conflicts *)

(** ** Conflicting events *)

(** Two events are conflicting if:

- One of them at least is a write
- They are different
- They affect the same location *)

Definition conflicting ex: rlt Event :=
  fun x y =>
    (In _ (evts ex) x) /\
    (In _ (evts ex) y) /\
    (is_write x \/ is_write y) /\
    x <> y /\
    (get_loc x) = (get_loc y).

(** Conflicting events of an execution belong to the events of this execution *)

Lemma conflicting_in_evts_left (ex: Execution) (x y: Event):
  conflicting ex x y ->
  In _ (evts ex) x.
Proof. compute; intuition auto. Qed.

Lemma conflicting_in_evts_right (ex: Execution) (x y: Event):
  conflicting ex x y ->
  In _ (evts ex) y.
Proof. compute; intuition auto. Qed.

(** If two events are conflicting, at least one of them is a write event *)

Lemma conflicting_one_is_write (ex: Execution) (x y: Event):
  conflicting ex x y ->
  is_write x \/ is_write y.
Proof. compute; intuition auto. Qed.

(** Two conflicting events are different *)

Lemma conflicting_diff (ex: Execution) (x y: Event):
  conflicting ex x y ->
  x <> y.
Proof. compute; intuition auto. Qed.

(** Two conflicting events affect the same location *)

Lemma conflicting_same_loc (ex: Execution) (x y: Event):
  conflicting ex x y ->
  get_loc x = get_loc y.
Proof. compute; intuition auto. Qed.

(** Two conflicting events must each be either a read or a write *)

Lemma conflicting_readwrite_l (ex: Execution) (x y: Event):
  conflicting ex x y ->
  (is_write x) \/ (is_read x).
Proof.
  intros Hconf. 
  apply conflicting_same_loc in Hconf as Hlocs.
  apply conflicting_one_is_write in Hconf as Hw.
  destruct x; destruct y; compute; intuition auto.
  inversion Hlocs.
Qed.

Lemma conflicting_readwrite_r (ex: Execution) (x y: Event):
  conflicting ex x y ->
  (is_write y) \/ (is_read y).
Proof.
  intros Hconf. 
  apply conflicting_same_loc in Hconf as Hlocs.
  apply conflicting_one_is_write in Hconf as Hw.
  destruct x; destruct y; compute; intuition auto.
  inversion Hlocs.
Qed.

(** If two events are conflicting in the prefix of an execution, they are
conflicting in the execution *)

Lemma conflicting_pre (pre ex: Execution) (x y: Event):
  prefix pre ex ->
  conflicting pre x y ->
  conflicting ex x y.
Proof.
  intros Hpre [Hinx [Hiny [Hiswrite [Hdiff Hloc]]]].
  repeat (apply conj); auto;
  apply (prefix_incl_evts _ _ Hpre); auto.
Qed.

(** Two events form a race if they are conflicting and if they are not related
by [hb] in any direction *)

Definition race (ex: Execution): rlt Event :=
  (conflicting ex) ⊓ (!(bidir (hb ex))).

(** Two events are pi-conflicting if they are conflicting, one of them at least
is not SC and they are not related by [(sb ⊔ rf_sc)⁺] in any direction *)

Definition at_least_one_not_sc: rlt Event :=
  fun x y => ~(get_mode x = Sc /\ get_mode y = Sc).

Definition pi (ex: Execution) : rlt Event :=
  (conflicting ex) ⊓
  at_least_one_not_sc ⊓
  (!(bidir (((sb ex) ⊔ (res_mode Sc (rf ex)))^+))).

(** Two pi-conflicting events are conflicting *)

Lemma pi_is_conflicting (ex: Execution) (x y: Event):
  (pi ex) x y -> (conflicting ex) x y.
Proof. intros [[? _] _]. auto. Qed.

(** Pi-conflicting events of an execution belong to the events of this 
execution *)

Lemma pi_in_evts_left (ex: Execution) (x y: Event):
  pi ex x y ->
  In _ (evts ex) x.
Proof. intros. eauto using conflicting_in_evts_left, pi_is_conflicting. Qed.

Lemma pi_in_evts_right (ex: Execution) (x y: Event):
  pi ex x y ->
  In _ (evts ex) y.
Proof. intros. eauto using conflicting_in_evts_right, pi_is_conflicting. Qed.

(** If two events are pi-conflicting, at least one of them is a write event *)

Lemma pi_one_is_write (ex: Execution) (x y: Event):
  pi ex x y ->
  is_write x \/ is_write y.
Proof. intros. eauto using conflicting_one_is_write, pi_is_conflicting. Qed.

(** Two pi-conflicting events are different *)

Lemma pi_diff (ex: Execution) (x y: Event):
  pi ex x y ->
  x <> y.
Proof. intros. eauto using conflicting_diff, pi_is_conflicting. Qed.

(** Two pi-conflicting events affect the same location *)

Lemma pi_same_loc (ex: Execution) (x y: Event):
  pi ex x y ->
  get_loc x = get_loc y.
Proof. intros. eauto using conflicting_same_loc, pi_is_conflicting. Qed.

(** If two events are pi-conflicting,at least one of them is SC *)

Lemma pi_at_least_one_not_sc (ex: Execution) (x y: Event):
  pi ex x y ->
  at_least_one_not_sc x y.
Proof. compute; intuition auto. Qed.

(** Two pi-conflicting events are not related by the transitive closure of the
union of sequenced-before and of read-from restricted to SC events in either
direction *)

Lemma pi_not_sbrfsc (ex: Execution) (x y: Event):
  pi ex x y ->
  ~((sb ex ⊔ (res_mode Sc (rf ex)))^+ x y).
Proof.
  compute; intuition auto.
Qed.

Lemma pi_not_cnv_sbrfsc (ex: Execution) (x y: Event):
  pi ex x y ->
  ~((sb ex ⊔ (res_mode Sc (rf ex)))^+ y x).
Proof.
  compute; intuition auto.
Qed.

(** When two events are pi-conflicting, they must each be either a read or a
write *)

Lemma pi_readwrite_l (ex: Execution) (x y: Event):
  pi ex x y ->
  (is_write x) \/ (is_read x).
Proof.
  intros Hpi. eapply conflicting_readwrite_l, pi_is_conflicting. eauto.
Qed.

Lemma pi_readwrite_r (ex: Execution) (x y: Event):
  pi ex x y ->
  (is_write y) \/ (is_read y).
Proof.
  intros Hpi. eapply conflicting_readwrite_r, pi_is_conflicting. eauto.
Qed.

(** For any execution, pi is a symmetric relation *)

Lemma pi_sym (ex: Execution) (x y: Event):
  (pi ex) x y <-> (pi ex) y x.
Proof. compute. intuition. Qed.

(** An execution is pi-conflicting if it contains two pi-conflicting events *)

Definition expi (ex: Execution) :=
  exists x y, (pi ex) x y.

Ltac solve_test_ineq :=
  unfold inj; simpl;
  intros x y [Heq Hmode]; split; auto;
  unfold Mse; unfold M in Hmode;
  destruct (get_mode x); simpl in *;
  intuition congruence.
  
(** ** SC-consistent prefixes *)

(** In a complete execution, the restriction of reads-from relation to SC events 
is included in the synchronises-with relation *)

Lemma nt_rfsc_incl_hb {ex: Execution}:
  valid_exec ex ->
  [M Sc] ⋅ rf ex ⋅ [M Sc] ≦  sw ex.
Proof.
  intros Hval.
  unfold sw.
  rewrite <- (one_incl_refl ([F]⋅sb ex)).
  rewrite <- (one_incl_refl (sb ex⋅[F])).
  rewrite !dot_one.
  apply incl_dot_test_right.
  solve_test_ineq.
  apply incl_dot_test_right.
  solve_test_ineq.
  rewrite <- !dotA.
  apply incl_dot_test_left.
  solve_test_ineq.
  rewrite 2dotA.
  unfold rs.
  rewrite <- (one_incl_refl (sb ex)).
  rewrite <- (one_incl_rtc (rf ex⋅rmw ex)).
  rewrite !dot_one, dtest.
  rewrite (rf_wr _ Hval) at 1.
  mrewrite (test_dot_comm _ R).
  apply incl_dot_test_right. auto.
  rewrite (test_in_one _ (M Sc)) at 2.
  rewrite (test_in_one _ R).
  rewrite !dot_one.
  apply incl_dot; auto.
  rewrite test_dot_comm.
  apply incl_dot; auto.
  solve_test_ineq.
Qed.

(** In a complete execution, the transitive closure of the union of the 
sequenced-before relation with restriction of the reads-from relation restricted
to SC events is included in the happens-before relation *)

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

(** In a complete execution, the transitive closure of the union of the
sequenced-before relation and reads-from relation restricted to SC events of the
prefix of an execution is included in the same relation in the execution *)

Lemma sbrfsc_incl_pre (pre ex: Execution):
  valid_exec ex ->
  prefix pre ex ->
  (sb pre ⊔ ([M Sc] ⋅ (rf pre) ⋅ [M Sc]))^+ ≦
  (sb ex ⊔ ([M Sc] ⋅ (rf ex) ⋅ [M Sc]))^+.
Proof.
  intros Hval Hpre.
  apply tc_incl.
  apply incl_cup.
  apply sb_prefix_incl; auto.
  apply incl_dot.
  apply incl_dot.
  solve_test_ineq.
  apply rf_prefix_incl; auto.
  solve_test_ineq.
Qed.

(** When the prefix of an execution doesn't contain any conflicting events, the
read-from relation of the prefix is included in the union of transitive closure 
of the union of the sequenced-before the reads-from restricted to SC events 
relations of this execution *)

Lemma rf_prefix_in_sbrfsc_ex {pre ex: Execution}:
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  ~(expi pre) ->
  (rf pre) ≦ (((sb ex) ⊔ ((res_mode Sc (rf ex))))^+).
Proof.
  intros Hval H11cons Hpre Hnoconflict x y Hrfpre.
(*   inversion Hcomp as [Hval _]. *)
  (* We suppose that x and y are related by ex.rf *)
  apply (rf_prefix_incl Hpre) in Hrfpre as Hrf.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { apply tc_incl_itself. right.
    exists y; try (exists x); try (apply M_get_mode_refl); auto;
    split; auto. }
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) x y)) 
    as [Hres | Hcontr]. { auto. }
  (* We suppose that x and y are not two sc events and that they are not
    related by ex.(sb U rf_sc)^+ *)
  exfalso.
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)^+ *)
  - destruct H11cons as [Hco _].
    apply (sbrfsc_incl_hb Hval) in Hres'.
    destruct (coherence_no_future_read _ Hco) with (x := x).
    eexists; eauto.
  (* If y and x are not related by ex.(sb U rf_sc)^+ *)
  - apply Hnoconflict. exists x,y.
    repeat (apply conj).
    + eapply rf_orig_evts; eauto.
      eauto using prefix_valid.
    + eapply rf_dest_evts; eauto.
      eauto using prefix_valid.
    + left. eauto using rf_orig_write.
    + intros Hnot. eapply (rf_irr _ Hval).
      split; eauto.
    + eapply rf_same_loc; eauto.
    + auto.
    + intros [Hn1 | Hn2].
      * eapply (sbrfsc_incl_pre _ ex) in Hn1; auto.
      * eapply (sbrfsc_incl_pre _ ex) in Hn2; auto.
Qed.

Lemma sbrf_incl_sbrfsc (ex: Execution):
  valid_exec ex ->
  rc11_consistent ex ->
  ~(expi ex) ->
  (sb ex ⊔ rf ex)^+ ≦ (sb ex ⊔ res_mode Sc (rf ex))^+.
Proof.
  intros Hval Hrc11 Hnotconf.
  erewrite (rf_prefix_in_sbrfsc_ex Hval Hrc11 _ Hnotconf) at 1.
  kat.
  Unshelve.
  apply prefix_itself.
  auto.
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
  ~(expi pre) ->
  (mo pre) ≦ ((((sb ex) ⊔ ((res_mode Sc (rf ex))))^+) ⊔ 
                               (res_mode Sc (mo ex))).
Proof.
  intros Hval H11cons Hpre Hnoconflict x y Hmopre.
  (* We suppose that x and y are related by ex.rf *)
  apply (mo_prefix_incl Hpre) in Hmopre as H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { right.
    exists y; try (exists x); try (apply M_get_mode_refl); auto;
    split; auto. }
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) x y)) 
    as [Hres | Hcontr]. { left. auto. }
  (* We suppose that x and y are not both sc events and that they are not
    related by ex.(sb U rf_sc)^+ *)
  exfalso.
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) y x)) 
    as [Hres' | Hcontr'].
  (* If y and x are related by ex.(sb U rf_sc)^+ *)
  - destruct H11cons as [Hco _].
    apply (sbrfsc_incl_hb Hval) in Hres'.
    destruct (coherence_coherence_ww _ Hco) with (x := x).
    eexists; eauto.
  (* If y and x are not related by ex.(sb U rf_sc)^+ *)
  - apply Hnoconflict. exists x,y.
    repeat (apply conj).
    + eapply mo_orig_evts; eauto.
      eauto using prefix_valid.
    + eapply mo_dest_evts; eauto.
      eauto using prefix_valid.
    + left. eauto using mo_orig_write.
    + intros Hnot. eapply (mo_irr _ Hval).
      split; eauto.
    + eapply mo_same_loc; eauto.
    + auto.
    + intros [Hn1 | Hn2].
      * eapply (sbrfsc_incl_pre _ ex) in Hn1; auto.
      * eapply (sbrfsc_incl_pre _ ex) in Hn2; auto.
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
  ~(expi pre) ->
  (rb pre) ≦ ((((sb ex) ⊔ ((res_mode Sc (rf ex))))^+) ⊔
                               (res_mode Sc (rb ex))).
Proof.
  intros Hval H11cons Hpre Hnoconflict x y Hrbpre.
  (* We suppose that x and y are related by ex.rf *)
  apply (rb_prefix_incl Hpre) in Hrbpre as H.
  destruct (classic ((get_mode x) = Sc /\ (get_mode y) = Sc)) 
    as [[Hxsc Hysc] | HNotSc].
  (* If x and y are Sc, then they are related by (ex.rf)_sc *)
  { right.
    exists y; try (exists x); try (apply M_get_mode_refl); auto; split; auto. }
  destruct (classic ((((sb ex) ⊔ (res_mode Sc (rf ex))) ^+) x y)) 
    as [Hres | Hcontr]. { left. auto. }
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
    eexists; try eexists; eauto.
  (* If y and x are not related by ex.(sb U rf_sc)^+ *)
  - apply Hnoconflict. exists x,y.
    repeat (apply conj).
    + eapply rb_orig_evts; eauto.
      eauto using prefix_valid.
    + eapply rb_dest_evts; eauto.
      eauto using prefix_valid.
    + right. eauto using rb_dest_write.
    + intros Hnot. eapply (rb_irr _ Hval).
      split; eauto.
    + eapply rb_same_loc; eauto.
    + auto.
    + intros [Hn1 | Hn2].
      * eapply (sbrfsc_incl_pre _ ex) in Hn1; auto.
      * eapply (sbrfsc_incl_pre _ ex) in Hn2; auto.
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
  intros Hval Hac.
  byabsurd. exfalso.
  rewrite (dcmp_in_res_neq_res Sc (sb ex)) in Hcontr.
  rewrite <- union_assoc in Hcontr.
  assert (acyclic (res_neq_mode Sc (sb ex))) as Hprob.
  { destruct_val_exec Hval. destruct Hsb_v as [Hlin _].
    apply lin_strict_ac in Hlin.
    apply ac_incl with (r1 := (res_neq_mode Sc (sb ex))) in Hlin.
    - auto.
    - apply res_neq_incl. }
  apply not_acyclic_is_cyclic in Hcontr.
  rewrite <-not_cyclic_is_acyclic in Hac.
  apply Hac.
  eapply (cycle_of_u_ac _ (res_neq_mode Sc (sb ex))).
  - intros w x y z H1 H2 H3.
    assert ((res_mode Sc (sb ex))^+ x y) as H.
    + unfold res_mode. apply tc_incl_itself.
      simpl_trt.
      * rewrite tc_inv_dcmp in H1. destruct H1 as [w2 _ [[[H1|H1]|H1]|H1]];
        apply res_mode_snd_mode in H1; unfold M; auto.
      * apply (tc_incl _ _ (res_neq_incl Sc (sb ex))) in H2.
        erewrite tc_of_trans in H2. auto.
        apply sb_trans; auto.
      * rewrite tc_inv_dcmp2 in H3. destruct H3 as [w2 [[[H3|H3]|H3]|H3] _];
        apply res_mode_fst_mode in H3; unfold M; auto.
    + incl_rel_kat H.
  - eauto.
  - destruct Hcontr as [w Hcontr].
    exists w. incl_rel_kat Hcontr.
Qed.

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

(** If there is a conflict in the prefix of an execution, there is a
conflict in the execution *)

Lemma sbrfsc_pre_inc (ex pre: Execution):
  prefix pre ex ->
  (sb pre ⊔ res_mode Sc (rf pre))^+ ≦ (sb ex ⊔ res_mode Sc (rf ex))^+.
Proof.
  intros Hpre.
  apply tc_incl.
  apply incl_cup.
  apply (sb_prefix_incl Hpre).
  apply res_mode_incl.
  apply (rf_prefix_incl Hpre).
Qed.

Lemma sbrf_pre_inc (ex pre: Execution):
  prefix pre ex ->
  (sb pre ⊔ rf pre)^+ ≦ (sb ex ⊔ rf ex)^+.
Proof.
  intros Hpre.
  apply tc_incl.
  apply incl_cup.
  apply (sb_prefix_incl Hpre).
  apply (rf_prefix_incl Hpre).
Qed.

(** If the prefix of an execution is pi-conflicting, the execution is 
pi-conflicting *)

Lemma pi_prefix_aux (pre ex: Execution):
  (forall a b, (sb ex ⊔ rf ex) a b -> In _ (evts pre) b -> In _ (evts pre) a) ->
  sb pre = [I (evts pre)]⋅sb ex⋅[I (evts pre)] ->
  rf pre = [I (evts pre)]⋅rf ex⋅[I (evts pre)] ->
  (forall x y, (sb ex ⊔ res_mode Sc (rf ex))^+ x y ->
               (fun w z => In _ (evts pre) w ->
                           In _ (evts pre) z ->
                           (sb pre ⊔ res_mode Sc (rf pre))^+ w z) x y).
Proof.
  intros Hclosed Hsb Hrf.
  apply tc_ind_right.
  - intros x y Hsbrfsc Hinx Hiny. apply tc_incl_itself.
    destruct Hsbrfsc; [left|right].
    + rewrite Hsb. simpl_trt. auto.
    + apply simpl_trt_hyp in H as [H1 [H2 H3]].
      unfold res_mode; simpl_trt.
      rewrite Hrf; simpl_trt. auto.
  - intros x y z Hxy Hyz IH2 Hin1 Hin2.
    assert (In _ (evts pre) y).
    { apply (Hclosed _ z); auto.
      apply (incl_rel_thm Hxy). unfold res_mode. kat. }
    apply tc_inv_dcmp7. exists y.
    + apply IH2; auto.
    + destruct Hxy as [Hxy|Hxy]; [left|right].
      * rewrite Hsb. simpl_trt. auto.
      * apply simpl_trt_hyp in Hxy as [H1 [H2 H3]].
        unfold res_mode; simpl_trt.
        rewrite Hrf; simpl_trt.
        auto.
Qed.

Lemma pi_prefix (ex pre: Execution) (x y: Event):
  prefix pre ex ->
  pi pre x y ->
  pi ex x y.
Proof.
  intros Hpre [[Hconf Hatsc] Hnotsbrf].
  inverse_prefix Hpre.
  unfold pi in *.
  split;[split|]; auto.
  - destruct Hconf as [H1 [H2 [H3 [H4 H5]]]].
    repeat (apply conj); auto.
  - intros [Hnot|Hnot]; apply Hnotsbrf; [left|right];
    destruct Hconf as [Hinx [Hiny _]].
    + eapply pi_prefix_aux; eauto.
    + rewrite <-cnv_rev. rewrite <-cnv_rev in Hnot.
      eapply pi_prefix_aux; eauto.
Qed.

Lemma expi_prefix (ex pre: Execution):
  prefix pre ex ->
  expi pre ->
  expi ex.
Proof.
  intros Hpre [x [y Hexpi]].
  exists x, y.
  apply (pi_prefix _ _ _ _ Hpre Hexpi).
Qed.

(** If the prefix of an RC11-concistent execution doesn't contain any pair of 
conflicting events, it is SC-consistent *)

Theorem no_conflict_prefix_sc : forall pre ex,
  valid_exec ex ->
  rc11_consistent ex ->
  prefix pre ex ->
  ~(expi pre) ->
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
  expi ex.
Proof.
  intros Hval Hrc11 Hsc. byabsurd.
  exfalso. apply Hsc.
  apply (no_conflict_prefix_sc ex ex); auto.
  apply prefix_itself. auto.
Qed.
