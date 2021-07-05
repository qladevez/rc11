(*
Abstraction of the strong DRF-SC proof through typeclasses.

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Classical_Prop.
Require Import Nat.
Require Import Lia.
From RC11 Require Import util.
From RC11 Require Import proprel_classic.
From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.

(** * Generic proof of weak and strong DRF-SC theorems *)

(** ** Definition of an event *)

Class Event Evt {Val Loc: Type} : Type :=
  {
    (* get the unique identifier of the event *)
    get_eid : Evt -> nat;
    (* get the location affected by the event *)
    loc : Evt -> option Loc;
    (* get the value read by the event *)
    get_read : Evt -> option Val;
    (* get the value written by the event *)
    get_written : Evt -> option Val;
    (* test if the event is a write *)
    W : prop_set Evt;
    (* test if the event is a read *)
    R : prop_set Evt;
    (* An event can't be both a read and a write *)
    not_randw: forall e, ~(R e /\ W e);
    (* If an event affects a location, it is either a read or a write *)
    loc_readwrite: forall e, (exists l, loc e = Some l) -> W e \/ R e;
    (* If an event is a write, it affects a location  *)
    loc_write: forall e, W e -> (exists l, loc e = Some l);
    (* If an event is a read, it affects a location *)
    loc_read: forall e, R e -> (exists l, loc e = Some l);
    (* If two events have the same event id, they are identical *)
    same_eid: forall e1 e2, get_eid e1 = get_eid e2 -> e1 = e2;
  }.

Section EventLemmas.
  Context {Evt:Type} `{Event Evt}.
  
  Lemma diff_evts_eid (e1 e2: Evt):
    e1 <> e2 -> get_eid e1 <> get_eid e2.
  Proof.
    intros Hdiff Hnot. apply Hdiff.
    apply same_eid. auto.
  Qed.
End EventLemmas.

(** ** Definition of a well-formed execution *)

Class Execution Ex {Evt: Type} `{Event Evt} : Type :=
  {
    (* events and relations of the execution *)
    evts (e: Ex) : Ensemble Evt;
    sb   (e: Ex) : rlt Evt;
    rf   (e: Ex) : rlt Evt;
    mo   (e: Ex) : rlt Evt;

    (* We need a constructor for executions *)
    mkex: Ensemble Evt -> rlt Evt -> rlt Evt -> rlt Evt -> Ex;

    (* We need this constructor to be correct *)
    mkex_evts (e: Ex) (e: Ensemble Evt) (r1 r2 r3: rlt Evt):
      evts (mkex e r1 r2 r3) = e;

    mkex_sb (e: Ex) (e: Ensemble Evt) (r1 r2 r3: rlt Evt):
      sb (mkex e r1 r2 r3) = r1;

    mkex_rf (e: Ex) (e: Ensemble Evt) (r1 r2 r3: rlt Evt):
      rf (mkex e r1 r2 r3) = r2;

    (* well-formedness of sequenced-before *)
    sb_diff {e: Ex}:
      forall e1 e2, (sb e) e1 e2 -> e1 <> e2;

    sb_l_evts {e: Ex}:
      forall e1 e2, (sb e) e1 e2 -> In _ (evts e) e1;

    sb_r_evts {e: Ex}:
      forall e1 e2, (sb e) e1 e2 -> In _ (evts e) e2;

    (* well-formedness of reads-from *)
    rf_same_loc {e: Ex}:
      forall e1 e2, (rf e) e1 e2 -> loc e1 = loc e2;

    rf_same_val {e:Ex}:
      forall e1 e2, (rf e) e1 e2 -> get_written e1 = get_read e2;

    rf_l_evts {e: Ex}:
      forall e1 e2, (rf e) e1 e2 -> In _ (evts e) e1;

    rf_r_evts {e: Ex}:
      forall e1 e2, (rf e) e1 e2 -> In _ (evts e) e2;

    rf_wr {e: Ex}:
      (rf e) = [W]⋅(rf e)⋅[R];

    rf_orig_unique {e: Ex}:
      forall e1 e2 e3, (rf e) e1 e3 -> (rf e) e2 e3 -> e1 = e2;

    (* well-formedness of modification-order *)
    mo_l_evts {e: Ex}:
      forall e1 e2, (mo e) e1 e2 -> In _ (evts e) e1;

    mo_r_evts {e: Ex}:
      forall e1 e2, (mo e) e1 e2 -> In _ (evts e) e2;

    mo_same_loc {e: Ex}:
      forall e1 e2, (mo e) e1 e2 -> loc e1 = loc e2;

    mo_ww {e: Ex}:
      (mo e) = [W]⋅(mo e)⋅[W];

    mo_diff {e: Ex}:
      forall e1 e2, (mo e) e1 e2 -> e1 <> e2;
  }.

Definition rb {Ex: Type} `{Execution Ex} (e: Ex) :=
  ((rf e)° ⋅ (mo e)).

(** ** Lemmas about well-formed executions *)

Section ExecutionsLemmas.
  Context {Ex:Type}.
  Context `{Execution Ex}.


  Lemma rf_l_write {e: Ex} {x y: Evt}:
    rf e x y -> W x.
  Proof.
    intros Hrf.
    rewrite rf_wr in Hrf.
    eapply simpl_trt_tleft.
    eauto.
  Qed.

  Lemma rf_r_read {e: Ex} {x y: Evt}:
    rf e x y -> R y.
  Proof.
    intros Hrf.
    rewrite rf_wr in Hrf.
    eapply simpl_trt_tright.
    eauto.
  Qed.

  Lemma rf_diff {e: Ex} {x y: Evt}:
    rf e x y -> x <> y.
  Proof.
    intros Hrf Heq.
    rewrite Heq in Hrf.
    apply rf_l_write in Hrf as Hw;
    apply rf_r_read in Hrf as Hr.
    eapply not_randw; eauto.
  Qed.

  Lemma mo_l_write {e: Ex} {x y: Evt}:
    mo e x y -> W x.
  Proof.
    intros Hmo.
    rewrite mo_ww in Hmo.
    eapply simpl_trt_tleft.
    eauto.
  Qed.

  Lemma rb_l_evts {e: Ex} {x y: Evt}:
    rb e x y ->
    In _ (evts e) x.
  Proof.
    intros [z Hrf _].
    rewrite <-cnv_rev in Hrf.
    eapply rf_r_evts; eauto.
  Qed.

  Lemma rb_r_evts {e: Ex} {x y: Evt}:
    rb e x y ->
    In _ (evts e) y.
  Proof.
    intros [z _ Hmo].
    eapply mo_r_evts; eauto.
  Qed.

  Lemma rb_rw {e: Ex}:
    rb e = [R]⋅rb e⋅[W].
  Proof.
    unfold rb. rewrite mo_ww, rf_wr.
    apply ext_rel. ra_simpl.
    repeat (rewrite injcnv).
    kat.
  Qed.

  Lemma rb_r_write {e: Ex} {x y: Evt}:
    rb e x y -> W y.
  Proof.
    intros Hrb.
    rewrite rb_rw in Hrb.
    eapply simpl_trt_tright.
    eauto.
  Qed.

  Lemma rb_l_read {e: Ex} {x y: Evt}:
    rb e x y -> R x.
  Proof.
    intros Hrb.
    rewrite rb_rw in Hrb.
    eapply simpl_trt_tleft.
    eauto.
  Qed.

  Lemma rb_same_loc {e: Ex} {x y: Evt}:
    rb e x y -> loc x = loc y.
  Proof.
    intros [z Hrf Hmo].
    rewrite <-cnv_rev in Hrf.
    apply rf_same_loc in Hrf.
    apply mo_same_loc in Hmo.
    congruence.
  Qed.

  Lemma rb_diff {e: Ex} {x y: Evt}:
    rb e x y -> x <> y.
  Proof.
    intros Hrb Heq.
    rewrite Heq in Hrb.
    apply rb_r_write in Hrb as Hw;
    apply rb_l_read in Hrb as Hr.
    eapply not_randw; eauto.
  Qed.

End ExecutionsLemmas.

(** ** Definition of a SC execution *)

Definition eco_sb {Ex: Type} `{Execution Ex} (e: Ex) :=
  (sb e) ⊔ (rf e) ⊔ (mo e) ⊔ (rb e).

Definition is_sc {Ex: Type} `{Execution Ex} (e: Ex) :=
  acyclic (eco_sb e). 

(** ** Definition of synchronization and races *)

Class HasSync Ex `{Execution Ex} : Type :=
  {
    sync (e: Ex) : rlt Evt;
    sync_trans {e: Ex} : sync e = (sync e)^+;
  }.

Section Races.

Context {Ex: Type}.
Context `{HasSync Ex}.

Definition race (e: Ex) (x y: Evt) :=
  (W x \/ W y) /\
  loc x = loc y /\
  x <> y /\
  ~(sync e x y) /\
  ~(sync e y x).

Lemma race_onewrite (e: Ex) (x y: Evt):
  race e x y ->
  (W x) \/ (W y).
Proof.
  compute; intuition auto.
Qed.

Lemma race_loc (e: Ex) (x y: Evt):
  race e x y ->
  loc x = loc y.
Proof.
  compute; intuition auto.
Qed.

Lemma race_diff (e: Ex) (x: Evt):
  ~(race e x x).
Proof.
  compute; intuition auto.
Qed.

Lemma race_diff' (e: Ex) (x y: Evt):
  race e x y ->
  x <> y.
Proof.
  intros Hrace Heq; rewrite Heq in Hrace; 
  eapply race_diff; eauto.
Qed.

Lemma race_syncxy (e: Ex) (x y: Evt):
  race e x y ->
  ~(sync e x y).
Proof.
  compute; intuition auto.
Qed.

Lemma race_syncyx (e: Ex) (x y: Evt):
  race e x y ->
  ~(sync e y x).
Proof.
  compute; intuition auto.
Qed.

Lemma race_readwrite_l (e: Ex) (x y: Evt):
  race e x y ->
  (W x) \/ (R x).
Proof.
  intros [[Hxw|Hyw] [Hsameloc _]]; apply loc_readwrite.
  - apply loc_write. auto.
  - apply loc_write in Hyw as [l' Hyloc].
    rewrite Hyloc in Hsameloc.
    exists l'; auto.
Qed.

Lemma race_readwrite_r (e: Ex) (x y: Evt):
  race e x y ->
  (W y) \/ (R y).
Proof.
  intros [[Hxw|Hyw] [Hsameloc _]]; apply loc_readwrite.
  - apply loc_write in Hxw as [l' Hxloc].
    rewrite Hxloc in Hsameloc.
    exists l'; auto.
  - apply loc_write. auto.
Qed.

Lemma race_sym (e: Ex) (x y: Evt):
  race e x y <-> race e y x.
Proof.
  split; intros [Hws [Hloc [Hsync1 Hsync2]]];
  repeat split; intuition auto.
Qed.

Definition racy (e: Ex) :=
  exists x y, race e x y.

Definition norace (e: Ex) :=
  forall x y, ~(race e x y).

Lemma racy_dcmp (e: Ex):
  racy e ->
  exists x y, race e x y /\
              get_eid x > get_eid y /\
              (W x \/ R x).
Proof.
  intros [w [z Hrace]].
  destruct (classic (get_eid w > get_eid z)) as [Hcomp|Hcomp].
  - exists w, z. split; [|split]; auto.
    eapply race_readwrite_l. eauto.
  - exists z, w. split; [|split].
    + apply race_sym; auto.
    + apply Compare_dec.not_gt, Compare_dec.le_lt_eq_dec in Hcomp.
      destruct Hcomp as [Hcomp|Hcomp].
      * lia.
      * apply same_eid in Hcomp. rewrite Hcomp in Hrace.
        exfalso. eapply race_diff. eauto.
    + eapply race_readwrite_r. eauto.
Qed.

End Races.

(** ** Definition of memory models that respect weak DRF-SC *)

Class WeakDRFSC Ex `{HasSync Ex} : Type :=
  {
    consistent : Ex -> Prop;

    (* The hypothesis is that we need
        - sync irreflexive
        - sync;rf irreflexive
        - sync;mo irreflexive
        - sync;rb irreflexive
        - sb ≤ sync
       But we will add the necessary lemmas when we need them in the proof
    *)

    sync_irr {e: Ex} : consistent e -> (forall x, ~(sync e x x));
    syncrf_irr {e: Ex} : consistent e -> (forall x, ~((sync e ⋅ rf e) x x));
    syncmo_irr {e: Ex} : consistent e -> (forall x, ~((sync e ⋅ mo e) x x));
    syncrb_irr {e: Ex} : consistent e -> (forall x, ~((sync e ⋅ rb e) x x));
    sb_incl_sync {e: Ex} : consistent e -> sb e ≦ sync e;
  }.

Section WeakDRF.
  Context {Ex: Type}.
  Context `{WeakDRFSC Ex}.

  Lemma norace_rf_incl_sync {e: Ex}:
    norace e ->
    consistent e ->
    rf e ≦ sync e.
  Proof.
    intros Hnorace Hcons x y Hrf.
    byabsurd. exfalso.
    destruct (classic (sync e y x)).
    - eapply (syncrf_irr Hcons).
      exists x; eauto.
    - apply (Hnorace x y).
      repeat split; eauto.
      + left. eauto using rf_l_write.
      + eauto using rf_same_loc.
      + eauto using rf_diff.
  Qed.

  Lemma norace_mo_incl_sync {e: Ex}:
    norace e ->
    consistent e ->
    mo e ≦ sync e.
  Proof.
    intros Hnorace Hcons x y Hmo.
    byabsurd. exfalso.
    destruct (classic (sync e y x)).
    - eapply (syncmo_irr Hcons).
      exists x; eauto.
    - apply (Hnorace x y).
      repeat split; eauto.
      + left. eauto using mo_l_write.
      + eauto using mo_same_loc.
      + eauto using mo_diff.
  Qed.

  Lemma norace_rb_incl_sync {e: Ex}:
    norace e ->
    consistent e ->
    rb e ≦ sync e.
  Proof.
    intros Hnorace Hcons x y Hmo.
    byabsurd. exfalso.
    destruct (classic (sync e y x)).
    - eapply (syncrb_irr Hcons).
      exists x; eauto.
    - apply (Hnorace x y).
      repeat split; eauto.
      + right. eauto using rb_r_write.
      + eauto using rb_same_loc.
      + eauto using rb_diff.
  Qed.

  Lemma weak_drf_sc (e: Ex):
    norace e ->
    consistent e -> 
    is_sc e.
  Proof.
    intros Hnorace Hcons x Hnot.
    apply (sync_irr Hcons x).
    apply (incl_rel_thm Hnot).
    unfold eco_sb.
    rewrite (sb_incl_sync Hcons).
    rewrite (norace_rf_incl_sync Hnorace Hcons).
    rewrite (norace_mo_incl_sync Hnorace Hcons).
    rewrite (norace_rb_incl_sync Hnorace Hcons).
    rewrite (sync_trans). kat.
  Qed.

  Lemma consistent_nonsc_imp_race (e: Ex):
    consistent e ->
    ~(is_sc e) ->
    racy e.
  Proof.
    intros Hcons Hnotsc.
    byabsurd. exfalso.
    apply Hnotsc, weak_drf_sc.
    - unfold norace. intros x y Hrace.
      apply Hcontr. exists x, y; auto.
    - auto.
  Qed.

End WeakDRF.

(** ** Definition of transformations of executions in a program *)

(** *** Bounding of an execution *)

Section SameProgram.

Context {Ex:Type} `{Execution Ex}.

Definition NLE (b: nat) : prop_set Evt :=
  fun e => b >= (get_eid e).

Lemma NLE_incl {b1 b2: nat}:
  b1 < b2 ->
  [NLE b1] ≦ [NLE b2].
Proof.
  intros Hord x y [Heq Hb1]. split; auto.
  unfold NLE in *. lia.
Qed.

Lemma NLE_dbl {b1 b2: nat}:
  b1 < b2 ->
  [NLE b1] = [NLE b1]⋅[NLE b2].
Proof.
  intros Hord. apply ext_rel, antisym; intros x y Hrel.
  - destruct Hrel as [Heq Hrel]. exists x; split; (try congruence).
    unfold NLE in *; lia.
  - incl_rel_kat Hrel.
Qed.

(** [be] is the execution [e] bounded by [n] *)

Definition b_ex (e be: Ex) (n: nat) :=
    evts be = (Intersection _ (evts e) (fun x => n >= get_eid x)) /\
    sb be = ([NLE n] ⋅ (sb e) ⋅ [NLE n]) /\
    rf be = ([NLE n] ⋅ (rf e) ⋅ [NLE n]) /\
    mo be = ([NLE n] ⋅ (mo e) ⋅ [NLE n]).

Lemma b_ex_evts {e be: Ex} {n: nat}:
  b_ex e be n ->
  evts be = Intersection _ (evts e) (fun x => n >= get_eid x).
Proof. compute; intuition auto. Qed.

Lemma b_ex_sb {e be: Ex} {n: nat}:
  b_ex e be n ->
  sb be = ([NLE n] ⋅ (sb e) ⋅ [NLE n]).
Proof. compute; intuition auto. Qed.

Lemma b_ex_rf {e be: Ex} {n: nat}:
  b_ex e be n ->
  rf be = ([NLE n] ⋅ (rf e) ⋅ [NLE n]).
Proof. compute; intuition auto. Qed.

Lemma b_ex_mo {e be: Ex} {n: nat}:
  b_ex e be n ->
  mo be = ([NLE n] ⋅ (mo e) ⋅ [NLE n]).
Proof. compute; intuition auto. Qed.

Lemma in_b_ex_eid (e be: Ex) (n: nat) (x: Evt):
  b_ex e be n ->
  In _ (evts be) x ->
  n >= get_eid x.
Proof.
  intros Hb Hin.
  destruct Hb as [Hevts _].
  rewrite Hevts in Hin.
  destruct Hin as [z _ Hord].
  unfold In in Hord. auto.
Qed.

Lemma b_ex_rb {e be: Ex} {n: nat}:
  b_ex e be n ->
  rb be ≦ ([NLE n]⋅rb e⋅[NLE n]).
Proof.
  intros Hb x y Hrel.
  unfold rb in *. destruct Hrel as [z H1 H2].
  rewrite <-cnv_rev in H1.
  rewrite (b_ex_rf Hb) in H1.
  rewrite (b_ex_mo Hb) in H2.
  apply simpl_trt_hyp in H1 as [H11 [H12 H13]].
  apply simpl_trt_hyp in H2 as [H21 [H22 H23]].
  exists y; [|split; auto].
  exists x; [split;auto|].
  exists z; auto.
Qed.

Lemma be_trans {e e1 e2: Ex} {m n: nat}:
  m < n ->
  b_ex e e1 n ->
  b_ex e e2 m ->
  b_ex e1 e2 m.
Proof.
  intros Hord Hb1 Hb2.
  repeat split.
  - rewrite (b_ex_evts Hb1), (b_ex_evts Hb2). 
    apply ext_set; intros x.
    apply antisym. 
    + intros [z Hset1 Hset2].
      unfold In in Hset2; split;[split|]; auto;
      unfold In; lia.
    + intros [z [z2 Hset1 Hset2] Hset3]; split; auto.
  - rewrite (b_ex_sb Hb1), (b_ex_sb Hb2).
    apply ext_rel, antisym; intros x y Hrel;
    [rewrite (NLE_dbl Hord) in Hrel|]; incl_rel_kat Hrel.
  - rewrite (b_ex_rf Hb1), (b_ex_rf Hb2).
    apply ext_rel, antisym; intros x y Hrel;
    [rewrite (NLE_dbl Hord) in Hrel|]; incl_rel_kat Hrel.
  - rewrite (b_ex_mo Hb1), (b_ex_mo Hb2). 
    apply ext_rel, antisym; intros x y Hrel;
    [rewrite (NLE_dbl Hord) in Hrel|]; incl_rel_kat Hrel.
Qed.

(** *** Execution equality modulo mo *)

Definition eq_modmo (e1 e2: Ex) :=
  evts e1 = evts e2 /\
  sb e1 = sb e2 /\
  rf e1 = rf e2.

(** *** Changing the write event a read reads from *)

(** [che] is [e] where the read [old_r] now reads from [new_w] *)

Definition ch_read (e che: Ex) (old_r new_r new_w: Evt) (v: Val) (l: Loc) :=
  (* We remove the old read and add the new read *)
  evts che = Union _ 
              (Intersection _ 
                (evts e) 
                (fun x => x <> old_r)) 
              (fun x => x = new_r) /\
  (* Everything linked to the old read by sb is now linked to the new read *)
  (sb che) = ((sb e \ ((fun x y => y = old_r) : rlt Evt)) ⊔ 
              (fun x y => (sb e x old_r) /\ y = new_r)) /\
  (* We remove the rf link between the old_r and its previous write and add
     a new rf link between the new write and the new read *)
  (rf che) = ((rf e \ ((fun x y => y = old_r) : rlt Evt)) ⊔ 
              (fun x y => x = new_w /\ y = new_r)) /\
  (* mo doesn't change *)
  (mo che) = (mo e).

(** Define the conditions of validity of such a change *)

Definition ch_read_valid (e: Ex) (old_r new_r new_w: Evt) (v: Val) (l: Loc) :=
  In _ (evts e) old_r /\
  In _ (evts e) new_w /\
  R old_r /\
  R new_r /\
  W new_w /\
  loc old_r = Some l /\
  loc new_r = Some l /\
  loc new_w = Some l /\
  get_read new_r = Some v /\
  get_written new_w = Some v.

(** *** What are the executions of a program *)

Inductive sameP (res ex: Ex) : Prop :=
  | sameP_bex : forall n, (b_ex ex res n) -> sameP res ex
  | sameP_ch_sbfin : forall old_r new_r new_w v l,
    (* The read we change is sb-final *)
    (forall x, ~(sb ex) old_r x) ->
    (* The change is valid *)
    ch_read_valid ex old_r new_r new_w v l ->
    ch_read ex res old_r new_r new_w v l ->
    sameP res ex
  | sameP_mo : eq_modmo res ex -> sameP res ex
  | sameP_trans : forall c, sameP res c -> sameP c ex -> sameP res ex.

Lemma sameP_ref (ex: Ex):
  sameP ex ex.
Proof.
  apply sameP_mo. compute; intuition auto.
Qed.

End SameProgram.

(** ** Strong DRF-SC *)

Class StrongDRFSC Ex `{WeakDRFSC Ex} : Type :=
  {
    (* Conditions to go from weak to strong DRF-SC *)

    (* 
    Since we need to transform our executions while preserving races, we need
    some hypothesis on our synchronisation relation.
    We propose the following hypothesis : the synchronisation relation is 
    independant of mo. This is coherent with the sync relation for SC, TSO and
    C11, which are all dependant only of sb and rf.
    *)

    sync_mo_ind: forall e1 e2, eq_modmo e1 e2 -> sync e1 = sync e2;

    (*
    In order to be able to turn an execution into another of the same program,
    we need to be able to take the prefixes of an execution. To do so, we force
    the unique identifiers of events to be such that bounding the identifiers
    of an execution creates a coherent prefix. We thus pose the following
    hypotheses on the identifiers of the events:
    - a write event has a strictly lower identifier than all the reads that read
      the value it writes to memory.
    - there is a relation deps of dependencies. This relation is a subset of
      the sequenced-before relation, and any event has a lower identifier than
      all the events that depend of it.

    Note that for these hypotheses to be true depends crucially on the model
    forbidding out-of-thin-air executions (by enforcing rf ⊔ deps being acyclic
    with an accurate notion of dependencies).
    *)

    rf_ord: forall e e1 e2, rf e e1 e2 -> get_eid e1 < get_eid e2;

    deps (e: Ex) : rlt Evt;
    deps_incl_sb: forall e, deps e ≦ sb e;
    deps_ord: forall e e1 e2, deps e e1 e2 -> get_eid e1 < get_eid e2;
  }. 

Section StrongDRF.
  Context {Ex:Type} `{StrongDRFSC Ex}.

Definition smallest_racy_b (e e2: Ex) (b: nat) :=
  b_ex e e2 b /\
  racy e2 /\
  (forall n e3, n < b ->
                b_ex e e3 n ->
                norace e3).

Axiom smallest_racy_b_exists:
  forall e, racy e ->
            (exists b e2, smallest_racy_b e e2 b).


(** *** Breaking a non-SC cycle by modifying the modification order *)

Definition last_evt_mo (mo: rlt Evt) (x: Evt) :=
  fun w1 w2 =>
          (w2 = x /\ loc w1 = loc w2) \/
          (w1 <> x /\ w2 <> x /\ mo w1 w2).

Definition change_mo (e: Ex) (x: Evt) :=
  mkex (evts e)
       (sb e)
       (rf e)
       (last_evt_mo (mo e) x).

Lemma change_mo_evts (e: Ex) (x: Evt):
  evts (change_mo e x) = evts e.
Proof.
  unfold change_mo. 
  rewrite (mkex_evts e (evts e) (sb e) (rf e) (last_evt_mo (mo e) x)).
  auto.
Qed.

Lemma change_mo_sb (e: Ex) (x: Evt):
  sb (change_mo e x) = sb e.
Proof.
  unfold change_mo. 
  rewrite (mkex_sb e (evts e) (sb e) (rf e) (last_evt_mo (mo e) x)).
  auto.
Qed.

Lemma change_mo_rf (e: Ex) (x: Evt):
  rf (change_mo e x) = rf e.
Proof.
  unfold change_mo.
  rewrite (mkex_rf e (evts e) (sb e) (rf e) (last_evt_mo (mo e) x)).
  auto.
Qed.

Lemma change_mo_eq_modmo (e: Ex) (x: Evt):
  eq_modmo (change_mo e x) e.
Proof.
  split;[|split].
  - rewrite change_mo_evts; auto.
  - rewrite change_mo_sb; auto.
  - rewrite change_mo_rf; auto.
Qed.

Lemma change_mo_sameP (e: Ex) (x: Evt):
  sameP (change_mo e x) e.
Proof.
  apply sameP_mo, change_mo_eq_modmo.
Qed.

Lemma change_mo_sync (e: Ex) (x: Evt):
  sync (change_mo e x) = sync e.
Proof.
  apply sync_mo_ind, change_mo_eq_modmo.
Qed.

Lemma change_mo_race (e: Ex) (x y z: Evt):
  race e x y ->
  race (change_mo e z) x y.
Proof.
  intros Hrace.
  repeat apply conj.
  - eauto using race_onewrite.
  - eauto using race_loc.
  - eauto using race_diff'.
  - intros Hsync.
    apply (race_syncxy _ _ _ Hrace).
    rewrite change_mo_sync in Hsync; auto.
  - intros Hsync.
    apply (race_syncyx _ _ _ Hrace).
    rewrite change_mo_sync in Hsync; auto.
Qed.


(** An non-SC-cycle passes through the last event of the
smallest non-SC bounding of an execution *)

Lemma eco_sb_diff (e: Ex) (x y: Evt):
  eco_sb e x y ->
  x <> y.
Proof.
  intros [[[Hsb|Hrf]|Hmo]|Hrb].
  - eauto using sb_diff.
  - eauto using rf_diff.
  - eauto using mo_diff.
  - eauto using rb_diff.
Qed.

Lemma eco_sb_in_evts_l (e: Ex) (x y: Evt):
  eco_sb e x y ->
  In _ (evts e) x.
Proof.
  intros Hrel.
  destruct Hrel as [[[Hsb|Hrf]|Hmo]|Hrb].
  - eapply sb_l_evts; eauto.
  - eapply rf_l_evts; eauto.
  - eapply mo_l_evts; eauto.
  - eapply rb_l_evts; eauto.
Qed.

Lemma eco_sb_in_evts_r (e: Ex) (x y: Evt):
  eco_sb e x y ->
  In _ (evts e) y.
Proof.
  intros Hrel.
  destruct Hrel as [[[Hsb|Hrf]|Hmo]|Hrb].
  - eapply sb_r_evts; eauto.
  - eapply rf_r_evts; eauto.
  - eapply mo_r_evts; eauto.
  - eapply rb_r_evts; eauto.
Qed. 

Lemma sc_cycle_in_evts_l (e: Ex) (x y: Evt):
  (eco_sb e)^+ x y ->
  In _ (evts e) x.
Proof.
  intros Hcyc.
  rewrite tc_inv_dcmp2 in Hcyc.
  destruct Hcyc as [w Hrel _].
  eapply eco_sb_in_evts_l; eauto.
Qed.

Lemma eco_sb_bnd_incl {e1 e2: Ex} {n: nat}:
  b_ex e1 e2 n ->
  (eco_sb e2) ≦ (eco_sb e1).
Proof.
  intros Hbe. unfold eco_sb.
  rewrite (b_ex_sb Hbe);
  rewrite (b_ex_rf Hbe);
  rewrite (b_ex_mo Hbe);
  rewrite (b_ex_rb Hbe).
  kat.
Qed.

Lemma eco_sb_bnd_incl_rev {e e1 e2: Ex} {x y: Evt} {m n: nat}:
  m < n ->
  b_ex e e1 n ->
  b_ex e e2 m ->
  eco_sb e1 x y ->
  get_eid x <= m ->
  get_eid y <= m ->
  eco_sb e2 x y.
Proof.
  intros Hord Hb1 Hb2 Hrel Hord1 Hord2.
  destruct Hrel as [[[Hrel|Hrel]|Hrel]|Hrel].
  - rewrite (b_ex_sb Hb1) in Hrel. apply simpl_trt_rel in Hrel.
    left; left; left. 
    rewrite (b_ex_sb Hb2); simpl_trt; auto;
    unfold NLE; lia.
  - rewrite (b_ex_rf Hb1) in Hrel. apply simpl_trt_rel in Hrel.
    left; left; right. 
    rewrite (b_ex_rf Hb2); simpl_trt; auto;
    unfold NLE; lia.
  - rewrite (b_ex_mo Hb1) in Hrel. apply simpl_trt_rel in Hrel.
    left; right. 
    rewrite (b_ex_mo Hb2); simpl_trt; auto;
    unfold NLE; lia.
  - destruct Hrel as [z Hrel1 Hrel2].
    rewrite <-cnv_rev, (b_ex_rf Hb1) in Hrel1. apply simpl_trt_rel in Hrel1.
    rewrite (b_ex_mo Hb1) in Hrel2. apply simpl_trt_rel in Hrel2.
    apply rf_ord in Hrel1 as Hord3.
    right. exists z.
    + rewrite <-cnv_rev, (b_ex_rf Hb2). simpl_trt; auto;
      unfold NLE; lia.
    + rewrite (b_ex_mo Hb2). simpl_trt; auto; unfold NLE; lia.
Qed.

Lemma eco_sb_nminone_lt_one {e e1: Ex} {x y: Evt} {n: nat}:
  b_ex e e1 n ->
  eco_sb e1 x y ->
  n-1 < n.
Proof.
  intros Hb Hrel.
  apply nminone_lt_n.
  destruct (Compare_dec.zerop n) as [Hzero|Hgtz]; auto.
  rewrite Hzero in Hb.
  apply eco_sb_in_evts_l in Hrel as Hx.
  apply eco_sb_in_evts_r in Hrel as Hy.
  rewrite (b_ex_evts Hb) in Hx, Hy.
  destruct Hx as [x _ Hx]. destruct Hy as [y _ Hy].
  unfold In in Hx, Hy.
  apply eco_sb_diff in Hrel. apply diff_evts_eid in Hrel.
  lia.
Qed.

Lemma eco_sb_e1_not_e2 {e e1 e2: Ex} {x y: Evt} {n: nat}:
  b_ex e e1 n ->
  b_ex e e2 (n-1) ->
  (eco_sb e1 \ eco_sb e2) x y ->
  (get_eid x = n \/ get_eid y = n).
Proof.
  intros Hb1 Hb2 [Hrel Hnotrel].
  destruct (Compare_dec.lt_eq_lt_dec n (get_eid x)) as [[Hord|Hord]|Hord].
  - apply eco_sb_in_evts_l in Hrel. rewrite (b_ex_evts Hb1) in Hrel.
    destruct Hrel as [z _ Hrel]. unfold In in Hrel. lia.
  - left; lia.
  - destruct (Compare_dec.lt_eq_lt_dec n (get_eid y)) as [[Hord'|Hord']|Hord'].
    + apply eco_sb_in_evts_r in Hrel. rewrite (b_ex_evts Hb1) in Hrel.
      destruct Hrel as [z _ Hrel]. unfold In in Hrel. lia.
    + right; lia.
    + exfalso; eapply Hnotrel.
      eapply (eco_sb_bnd_incl_rev (eco_sb_nminone_lt_one Hb1 Hrel)); eauto; lia.
Qed.

Lemma smallest_b_sc_cycle_last_evt (e e1 e2: Ex) (x:Evt) (n: nat):
  get_eid x = n ->
  b_ex e e1 n ->
  b_ex e e2 (n-1) ->
  ~(is_sc e1) ->
  is_sc e2 ->
  (eco_sb e1)^+ x x.
Proof.
  intros Heid Hb1 Hb2 Hnotsc Hsc.
  apply not_acyclic_is_cyclic in Hnotsc.
  destruct Hnotsc as [z Hcyc].
  apply (cycle_ext _ (eco_sb e2)) in Hcyc.
  rewrite union_comm in Hcyc.
  apply (added_cycle_pass_through_addition2 _ _ _ Hsc) in Hcyc.
  destruct Hcyc as [y [w Hres Hcycrest]].
  destruct (eco_sb_e1_not_e2 Hb1 Hb2 Hres) as [Hy|Hw].
  - rewrite <-Hy in Heid. apply same_eid in Heid. rewrite Heid.
    destruct Hres as [Hres _].
    apply (be_trans (eco_sb_nminone_lt_one Hb1 Hres) Hb1) in Hb2.
    apply (incl_unionincl_rtc _ _ (eco_sb_bnd_incl Hb2)) in Hcycrest.
    incl_rel_kat (cmp_seq Hres Hcycrest).
  - rewrite <-Hw in Heid. apply same_eid in Heid. rewrite Heid.
    destruct Hres as [Hres _].
    apply (be_trans (eco_sb_nminone_lt_one Hb1 Hres) Hb1) in Hb2.
    apply (incl_unionincl_rtc _ _ (eco_sb_bnd_incl Hb2)) in Hcycrest.
    incl_rel_kat (cmp_seq Hcycrest Hres).
Qed.

Lemma drf (e: Ex):
  (exists e2, sameP e2 e /\
              consistent e2 /\
              ~(is_sc e2)) ->
  (exists e2, sameP e2 e /\
              is_sc e2 /\
              (exists x y, race e2 x y)).
Proof.
  intros [e2 [Hsame [Hcons Hnotsc]]].
  pose proof (consistent_nonsc_imp_race _ Hcons Hnotsc) as Hracy.
  apply smallest_racy_b_exists in Hracy as [b [e3 [Hbound [Hracy Hsmallest]]]].
  apply racy_dcmp in Hracy as [x [y [Hrace [Hord Hxwr]]]]. 
  destruct Hxwr as [Hwrite|Hread].
  - exists (change_mo e3 x).
    split;[|split].
    + eapply sameP_trans. 
      * eapply change_mo_sameP.
      * eapply sameP_trans; eauto.
        eapply sameP_bex; eauto.
    + 
    + exists x, y.
      eapply change_mo_race. eauto.
  - admit.
Admitted.

Lemma drf_final (e: Ex):
  (forall e2, sameP e2 e ->
              is_sc e2 ->
              norace e2) ->
  (forall e2, sameP e2 e ->
              consistent e2 ->
              is_sc e2).
Proof.
  intros Hnorace ex2 Hsame Htso x Hcyc.
  unshelve (epose proof (drf ex2 _) as [ex3 [Hsame2 [Hsc [w1 [w2 Hrace]]]]]).
  { exists ex2. split;[|split].
    - auto using sameP_ref.
    - auto.
    - intros Hnot. eapply Hnot. eauto.
  }
  eapply (Hnorace ex3); eauto.
  eapply sameP_trans; eauto.
Qed.
