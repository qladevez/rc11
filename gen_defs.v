(* 
Abstraction of the strong DRF-SC proof through typeclasses.

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Classical_Prop.
Require Import Nat.
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
    get_loc : Evt -> option Loc;
    (* get the value read by the event *)
    get_read : Evt -> option Val;
    (* get the value written by the event *)
    get_written : Evt -> option Val;
    (* test if the event is a write *)
    W : prop_set Evt;
    (* test if the event is a read *)
    R : prop_set Evt;
    (* If an event affects a location, it is either a read or a write *)
    loc_readwrite: forall e, (exists l, get_loc e = Some l) -> W e \/ R e;
  }.

(** ** Definition of a well-formed execution *)

Class Execution Ex {Evt: Type} `{Event Evt} : Type :=
  {
    (* events and relations of the execution *)
    evts (e: Ex) : Ensemble Evt;
    sb   (e: Ex) : rlt Evt;
    rf   (e: Ex) : rlt Evt;
    mo   (e: Ex) : rlt Evt;

    (* well-formedness of reads-from *)
    rf_same_loc {e: Ex}:
      forall e1 e2, (rf e) e1 e2 -> get_loc e1 = get_loc e2;

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
    mo_same_loc {e: Ex}:
      forall e1 e2, (mo e) e1 e2 -> get_loc e1 = get_loc e2;

    mo_ww {e: Ex}:
      (mo e) = [W]⋅(mo e)⋅[W];
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

  Lemma mo_l_write {e: Ex} {x y: Evt}:
    mo e x y -> W x.
  Proof.
    intros Hmo.
    rewrite mo_ww in Hmo.
    eapply simpl_trt_tleft.
    eauto.
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

  Lemma rb_same_loc {e: Ex} {x y: Evt}:
    rb e x y -> get_loc x = get_loc y.
  Proof.
    intros [z Hrf Hmo].
    rewrite <-cnv_rev in Hrf.
    apply rf_same_loc in Hrf.
    apply mo_same_loc in Hmo.
    congruence.
  Qed.

End ExecutionsLemmas.

(** ** Definition of a SC execution *)

Definition is_sc {Ex: Type} `{Execution Ex} (e: Ex) :=
  acyclic ((sb e) ⊔ (rf e) ⊔ (mo e) ⊔ (rb e)). 

(** ** Definition of synchronization and races *)

Class HasSync Ex `{Execution Ex} : Type :=
  {
    sync (e: Ex) : rlt Evt;
    sync_trans {e: Ex} : sync e = (sync e)^+;
    
  }.

Definition race {Ex: Type} `{HasSync Ex} (e: Ex) (x y: Evt) :=
  (W x \/ W y) /\
  get_loc x = get_loc y /\
  ~(sync e x y) /\
  ~(sync e y x).

Definition racy {Ex:Type} `{HasSync Ex} (e: Ex) :=
  exists x y, race e x y.

Definition norace {Ex:Type} `{HasSync Ex} (e: Ex) :=
  forall x y, ~(race e x y).

Lemma race_readwrite_l {Ex: Type} `{HasSync Ex} (e: Ex) (x y: Evt):
  race e x y ->
  (R x) \/ (W x).
Proof.
  intros Hrace.
Admitted.

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
  Qed.

  Lemma weak_drf_sc (e: Ex):
    norace e ->
    consistent e -> 
    is_sc e.
  Proof.
    intros Hnorace Hcons x Hnot.
    apply (sync_irr Hcons x).
    apply (incl_rel_thm Hnot).
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

(** [be] is the execution [e] bounded by [n] *)

Definition b_ex (e be: Ex) (n: nat) :=
    evts be = (Intersection _ (evts e) (fun x => n >= get_eid x)) /\
    sb be = ([NLE n] ⋅ (sb e) ⋅ [NLE n]) /\
    rf be = ([NLE n] ⋅ (rf e) ⋅ [NLE n]) /\
    mo be = ([NLE n] ⋅  (mo e) ⋅ [NLE n]).

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
  get_loc old_r = Some l /\
  get_loc new_r = Some l /\
  get_loc new_w = Some l /\
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
  }.

Section StrongDRF.
  Context {Ex:Type} `{StrongDRFSC Ex}.

Definition smallest_racy_b (e: Ex) (b: nat) :=
  racy e /\
  (forall n e2, (b_ex e e2 b) ->
                racy e2 ->
                n >= b).

Axiom smallest_racy_b_exists:
  forall e, racy e ->
            (exists b e2, smallest_racy_b e2 b).

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
  apply smallest_racy_b_exists in Hracy 
    as [n [e3 [Hracy Hsmallest]]].

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
