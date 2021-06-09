(* 
Formalisation of the DRF-SC Property for x86-TSO

Author: Quentin Ladeveze, Inria Paris, France
*)

Require Import Ensembles.
Require Import Classical_Prop.
Require Import Nat.
From RC11 Require Import util.
From RC11 Require Import proprel_classic.
From RC11 Require Import gen_defs.
From RelationAlgebra Require Import 
  lattice prop monoid rel kat_tac normalisation kleene kat rewriting.

Open Scope rel_notations.

(** * x86-TSO and DRF-SC *)

(** ** x86-TSO executions *)

(** We abstract from word-size and alignment issues for now,
representing both memory locations and the values that may be
stored in them by natural numbers. *)

Definition Word := nat.

Definition Loc : Type := Word.

Definition Val : Type := Word.

(** ** Events *)

(** An event can be:

- A read of a value at a location
- A write of a value at a location
- A read-modify-write of a read value and written value at a location
- A fence

Every single event has a unique event id.
*)

Inductive Event : Type :=
| Read (eid: nat) (l: Loc) (v: Val)
| Write (eid: nat) (l: Loc) (v: Val)
| Rmw (eid: nat) (l: Loc) (rv: Val) (wv: Val)
| Fence (eid: nat).

Definition get_eid (evt: Event) :=
  match evt with
  | Read e _ _ => e
  | Write e _ _ => e
  | Rmw e _ _ _ => e
  | Fence e => e
  end.

Definition get_loc (evt: Event) :=
  match evt with
  | Read _ l _ => Some l
  | Write _ l _ => Some l
  | Rmw _ l _ _ => Some l
  | Fence _ => None
  end.

Definition get_read (evt: Event) :=
  match evt with
  | Read _ _ v => Some v
  | Rmw _ _ v _ => Some v
  | _ => None
  end.

Definition get_written (evt: Event) :=
  match evt with
  | Write _ _ v => Some v
  | Rmw _ _ _ v => Some v
  | _ => None
  end.

(** * Basic relations *)

(** ** Identity relations *)

Definition E : prop_set Event := top.

Definition R : prop_set Event :=
  fun e =>
    match e with
    | Read _ _ _ => top
    | _ => bot
    end.

Definition W : prop_set Event :=
  fun e =>
    match e with
    | Write _ _ _ => top
    | _ => bot
    end.

Definition U : prop_set Event :=
  fun e =>
    match e with
    | Rmw _ _ _ _ => top
    | _ => bot
    end.

Definition F : prop_set Event :=
  fun e =>
    match e with
    | Fence _ => top
    | _ => bot
    end.

Definition reads (evts: Ensemble Event) :=
  In _ (Union _ R evts).

Definition writes (evts: Ensemble Event) :=
  In _ (Union _ W evts).

Definition rmws (evts: Ensemble Event) :=
  In _ (Union _ U evts).

Definition fences (evts: Ensemble Event) :=
  In _ (Union _ F evts).

Instance tso_is_event : (@gen_defs.Event tso.Event Val Loc) :=
  {
    get_loc := get_loc;
    get_read := get_read;
    get_written := get_written;
    W := W;
    R := R
  }.

(** ** Executions *)

Record Execution : Type := mkex {
  evts : Ensemble Event;
  sb : rlt Event;
  rf : rlt Event;
  mo : rlt Event;
}.

Definition valid_evts (evts: Ensemble Event) (sb rf: rlt Event) :=
  (forall e1 e2, (In _ evts e1) -> (In _ evts e2) ->
    (get_eid e1) <> (get_eid e2) \/ e1 = e2) /\
  (forall e1 e2, (sb ⊔ rf) e1 e2 ->
    get_eid e1 < get_eid e2).

Definition valid_sb (evts: Ensemble Event) (sb : rlt Event) : Prop :=
  (partial_order sb evts) /\
  (forall (l : Loc),
  exists (e: Event) (eid: nat),
    e = Write eid l zero /\
    ~(In _ (ran sb) e) /\
    forall e', In _ (ran sb) e' -> sb e e').

Definition valid_rf (evts : Ensemble Event) (rf : rlt Event) : Prop :=
  (forall w r, 
    rf w r ->
    ((get_loc w) = (get_loc r) /\
     (get_written w) = (get_read r))) /\
  (rf = [I evts] ⋅ rf ⋅ [I evts]) /\
  ([W ⊔ U]⋅rf⋅[R ⊔ U] = rf) /\
  (forall w1 w2 r,
    (rf w1 r) /\ (rf w2 r) -> w1 = w2).

Definition valid_mo (evts: Ensemble Event) (mo : rlt Event) : Prop :=
  ([W ⊔ U]⋅mo⋅[W ⊔ U] = mo) /\
  (forall x y, mo x y ->
               (get_loc x) = (get_loc y)) /\
  (partial_order mo evts) /\
  (total_rel mo (Union _ (writes evts) (Union _ (rmws evts) (fences evts)))).

Definition valid_exec (e: Execution) : Prop :=
  (* valid events mode *)
  valid_evts e.(evts) e.(sb) e.(rf) /\
  (* sequenced-before is valid *)
  valid_sb e.(evts) e.(sb) /\
  (* reads-from is valid *)
  valid_rf e.(evts) e.(rf) /\
  (* modification order is valid *)
  valid_mo e.(evts) e.(mo) /\
  (* Execution is complete *)
  Included _ (reads (evts e)) (ran e.(rf)).
 
Ltac destruct_val_exec H :=
  destruct H as [Hevts_v [Hsb_v [Hrf_v [Hmo_v Hcomp]]]].

Ltac inverse_val_exec H :=
  inversion H as [Hevts_v [Hsb_v [Hrf_v [Hmo_v Hcomp]]]].

Lemma rf_loc (ex: Execution) (x y: Event):
  valid_exec ex ->
  rf ex x y ->
  get_loc x = get_loc y.
Proof.
  intros Hval Hrf.
  destruct_val_exec Hval.
  destruct Hrf_v as [Hrf_v _].
  apply Hrf_v. auto.
Qed.

Lemma mo_write_r (ex: Execution) (x y: Event):
  valid_exec ex ->
  mo ex x y ->
  (W ⊔ U) y.
Proof.
  intros Hval Hmo.
  destruct_val_exec Hval.
  destruct Hmo_v as [Hmo_v _].
  rewrite <-Hmo_v in Hmo.
  destruct Hmo as [z _ Hmo].
  destruct Hmo as [Heq Hmo].
  rewrite Heq in Hmo. auto.
Qed.

Lemma mo_diff (ex: Execution) (x y: Event):
  valid_exec ex ->
  mo ex x y ->
  x <> y.
Proof.
  intros Hval Hmo Heq.
  destruct_val_exec Hval.
  destruct Hmo_v as [_ [_ [Hmopo _]]].
  destruct Hmopo as [_ [_ Hmoirr]].
  apply (Hmoirr y). rewrite Heq in Hmo. auto.
Qed.

Lemma mo_loc (ex: Execution) (x y: Event):
  valid_exec ex ->
  mo ex x y ->
  get_loc x = get_loc y.
Proof.
  intros Hval Hmo.
  destruct_val_exec Hval. destruct Hmo_v as [_ [Hmo_v _]].
  auto.
Qed.

(** ** Derived relations *)

Definition rb (ex: Execution) :=
  ((rf ex)° ⋅ mo ex) \ [E].

Lemma rb_write_r (ex: Execution) (x y: Event):
  valid_exec ex ->
  rb ex x y ->
  (W ⊔ U) y.
Proof.
  intros Hval [[z _ Hmo] _].
  eapply mo_write_r; eauto.
Qed.

Lemma rb_diff (ex: Execution) (x y: Event):
  rb ex x y ->
  x <> y.
Proof.
  intros Hrb Heq.
  destruct Hrb as [_ Ht]. eapply Ht.
  split; unfold E; simpl; eauto.
Qed.

Lemma rb_loc (ex: Execution) (x y: Event):
  valid_exec ex ->
  rb ex x y ->
  get_loc x = get_loc y.
Proof.
  intros Hval [[z Hrf Hmo] _].
  apply cnv_rev in Hrf.
  apply (rf_loc _ _ _ Hval) in Hrf.
  apply (mo_loc _ _ _ Hval) in Hmo.
  congruence.
Qed.

Definition com (ex: Execution) : rlt Event :=
  (rf ex) ⊔ (mo ex) ⊔ (rb ex).

Definition hb (ex: Execution) : rlt Event :=
  (sb ex ⊔ rf ex)^+.

(** ** Consistency *)

Definition sc_consistent (ex: Execution) :=
  acyclic (sb ex ⊔ rf ex ⊔ mo ex ⊔ rb ex).

Definition tso_consistent (ex: Execution) :=
  (* hb is irreflexive *)
  (forall x, ~(hb ex) x x) /\
  (* mo;hb is irreflexive *)
  (forall x, ~(mo ex⋅hb ex) x x) /\
  (* rb;hb is irreflexive *)
  (forall x, ~(rb ex⋅hb ex) x x) /\
  (* rb;mo is irreflexive *)
  (forall x, ~(rb ex⋅mo ex) x x) /\
  (* rb;mo;(rf\sb);sb is irreflexive *)
  (forall x, ~(rb ex⋅mo ex⋅(rf ex\sb ex)⋅sb ex) x x) /\
  (* rb;mo;[U ⊔ F];sb is irreflexive *)
  (forall x, ~(rb ex⋅mo ex⋅[U ⊔ F]⋅sb ex) x x).

Lemma tso_hb_irr (ex: Execution):
  tso_consistent ex ->
  (forall x, ~(hb ex) x x).
Proof.
  compute; intuition eauto.
Qed.

Lemma tso_mohb_irr (ex: Execution):
  tso_consistent ex ->
  (forall x, ~(mo ex⋅hb ex) x x).
Proof.
  compute; intuition eauto.
Qed.

Lemma tso_rbhb_irr (ex: Execution):
  tso_consistent ex ->
  (forall x, ~(rb ex⋅hb ex) x x).
Proof.
  compute; intuition eauto.
Qed.

(** ** Alternative consistency 

Alternative definition of the TSO model from (A Shared Memory Poetics, 
Alglave J., 2010). We'll try to show that both definitions of the memory
model are equivalents
*)

(** sequenced-before restricted to events affecting the same location *)

Definition sb_loc (ex: Execution) : rlt Event :=
  fun x => fun y =>
    (sb ex x y) /\ (get_loc x = get_loc y).

(** The subset of sequenced-before preserved by the model *)

Definition psb_tso (ex: Execution) :=
  ([R]⋅sb ex⋅[E]) ⊔ ([W]⋅sb ex⋅[W]).

(** The subset of reads-from preserved by the model.
The external reads-from, 
a.k.a. the relating events from different procs
a.k.a. the one not related by sequenced-before in any direction *)

Definition rfe (ex: Execution) :=
  (rf ex) \ (sb ex ⊔ (sb ex)°).

(** Global happens-before *)

Definition ghb_tso (ex: Execution) :=
  (psb_tso ex) ⊔ (rfe ex) ⊔ (mo ex) ⊔ (rb ex).


(** *** Conditions *)

(** Uniproc condition or sc-by-location *)

Definition uniproc_tso (ex: Execution) :=
  acyclic (sb_loc ex ⊔ com ex).

Definition oota_tso (ex: Execution) :=
  acyclic (sb ex ⊔ rf ex).

Definition ghb_ac_tso (ex: Execution) :=
  acyclic (ghb_tso ex).

Definition tso_consistent_alt (ex: Execution) :=
  uniproc_tso ex /\
  oota_tso ex /\
  ghb_ac_tso ex.

Lemma tso_consistent_alt_ghb_ac (ex: Execution):
  tso_consistent_alt ex -> ghb_ac_tso ex.
Proof.
  compute; intuition auto.
Qed.

Lemma tso_consistent_alt_oota (ex: Execution):
  tso_consistent_alt ex -> oota_tso ex.
Proof.
  compute; intuition auto.
Qed.


(** *** Proof of equivalent between the two definitions of TSO *)

(** In a tso-consistent execution, [hb] is the transitive closure of the union 
of sequenced-before and external reads-from *)

Lemma hb_sbrfe (ex: Execution):
  tso_consistent_alt ex ->
  hb ex ≦ (sb ex ⊔ rfe ex)^+.
Proof.
  intros Htso. unfold hb.
  apply tc_incl, union_incl.
  - kat.
  - intros x y Hrf.
    destruct (classic (sb ex x y)) as [Hxy|Hxy].
    + incl_rel_kat Hxy.
    + destruct (classic ((sb ex)° x y)) as [Hyx|Hyx].
      * eapply tso_consistent_alt_oota in Htso. exfalso; eapply Htso.
        eapply tc_trans; [incl_rel_kat Hrf|].
        apply cnv_rev in Hyx. incl_rel_kat Hyx.
      * right. split; [incl_rel_kat Hrf|].
        compute; intuition auto.
Qed.

Lemma equiv_tso_consistencies (ex: Execution):
  tso_consistent ex <-> tso_consistent_alt ex.
Proof.
  split; intros Hval; repeat (apply conj).
  - admit.
  - compute in *; intuition auto.
  - admit.
  - intros x H.
    apply tso_consistent_alt_oota in Hval.
    eapply Hval. unfold hb in H. incl_rel_kat H.
  - intros x H.
    destruct H as [z Hmo Hhb].
    apply (hb_sbrfe ex Hval) in Hhb.
    apply tso_consistent_alt_ghb_ac in Hval.
    eapply Hval.
    apply (incl_rel_thm (cmp_seq Hmo Hhb)). 
    unfold ghb_tso, psb_tso. kat.

(** ** Race *)

Definition race (ex: Execution) : rlt Event :=
  fun x => fun y => 
    ((W ⊔ U) x \/ (W ⊔ U) y) /\
    x <> y /\
    get_loc x = get_loc y /\
    ~((hb ex) x y) /\
    ~((hb ex) y x).

Definition norace (ex: Execution) :=
  forall x y, ~race ex x y.

(** ** Weak DRF-SC *)

Lemma weak_drf_sc (ex: Execution):
  valid_exec ex ->
  tso_consistent ex ->
  (forall x y, ~(race ex x y)) ->
  sc_consistent ex.
Proof.
  intros Hval Htso Hnorace.
  intros x Hcyc.
  apply (tso_hb_irr ex Htso x).
  apply (incl_rel_thm Hcyc).
  apply tc_incl_2; apply union_incl; [apply union_incl|].
  - kat.
  - intros y z Hmo. destruct (classic (hb ex y z)) as [Hhb|Hnothb].
    + unfold hb in Hhb; incl_rel_kat Hhb.
    + exfalso. apply (Hnorace y z). repeat split.
      * right. eapply mo_write_r; eauto.
      * eapply mo_diff; eauto.
      * eapply mo_loc; eauto.
      * auto.
      * intros Hnot. eapply (tso_mohb_irr ex Htso y).
        exists z; eauto.
  - intros y z Hmo. destruct (classic (hb ex y z)) as [Hhb|Hnothb].
    + unfold hb in Hhb; incl_rel_kat Hhb.
    + exfalso. apply (Hnorace y z). repeat split.
      * right. eapply rb_write_r; eauto.
      * eapply rb_diff; eauto.
      * eapply rb_loc; eauto.
      * auto.
      * intros Hnot. eapply (tso_rbhb_irr ex Htso y).
        exists z; eauto.
Qed.

(** ** Axiomatisation of the executions of a program *)

(** *** Bouding of an execution *)

Definition NLE (b: nat) : prop_set Event :=
  fun e => b >= (get_eid e).

Definition b_ex (ex: Execution) (n: nat) := mkex
    (Intersection _ (evts ex) (fun x => n >= get_eid x))
    ([NLE n] ⋅ (sb ex) ⋅ [NLE n])
    ([NLE n] ⋅ (rf ex) ⋅ [NLE n])
    ([NLE n] ⋅  (mo ex) ⋅ [NLE n]).

(** *** Execution equality modulo mo *)

Definition eq_modmo (e1 e2: Execution) :=
  evts e1 = evts e2 /\
  sb e1 = sb e2 /\
  rf e1 = rf e2.

(** *** Changing a sb-final read in an execution *)

(** Changing the write event a read reads from *)

Definition ch_read (ex: Execution) (old_r new_w: Event) (v: Val) (l: Loc) :=
  let new_r := Read (get_eid old_r) l v in mkex
  (* We remove the old read and add the new read *)
  (Union _ (Intersection _ (evts ex) (fun x => x <> old_r)) (fun x => x = new_r))
  (* Everything linked to the old read by sb is now linked to the new read *)
  ((sb ex \ ((fun x y => y = old_r) : rlt Event)) ⊔ (fun x y => (sb ex x old_r) /\ y = new_r))
  (* We remove the rf link between the old_r and its previous write and add
     a new rf link between the new write and the new read *)
  ((rf ex \ ((fun x y => y = old_r) : rlt Event)) ⊔ (fun x y => x = new_w /\ y = new_r))
  (* mo doesn't change *)
  (mo ex).

(** Define the conditions of validity of such a change *)

Definition ch_read_valid (ex: Execution) (old_r new_w: Event) (v: Val) (l: Loc) :=
  In _ (evts ex) old_r /\
  In _ (evts ex) new_w /\
  R old_r /\
  W new_w /\
  get_loc old_r = Some l /\
  get_loc new_w = Some l /\
  get_written new_w = Some v.

(** What are the executions of a program *)

Inductive sameP (res ex: Execution) : Prop :=
  | sameP_bex : forall n, res = (b_ex ex n) -> sameP res ex
  | sameP_ch_sbfin : forall old_r new_w v l,
    (* The read we change is sb-final *)
    (forall x, ~(sb ex) old_r x) ->
    (* The change is valid *)
    ch_read_valid ex old_r new_w v l ->
    res = ch_read ex old_r new_w v l ->
    sameP res ex
  | sameP_mo : eq_modmo res ex -> sameP res ex
  | sameP_trans : forall c, sameP res c -> sameP c ex -> sameP res ex.

(* sameP is reflexive *)

Lemma sameP_ref (ex: Execution):
  sameP ex ex.
Proof.
  apply sameP_mo. compute; intuition auto.
Qed.

Lemma drf (ex: Execution):
  (exists ex2, sameP ex2 ex /\
               tso_consistent ex2 /\
               ~(sc_consistent ex2)) ->
  (exists ex2, sameP ex2 ex /\
               sc_consistent ex2 /\
               (exists x y, race ex2 x y)).
Proof.
Admitted.

Lemma drf_final (ex: Execution):
  (forall ex2, sameP ex2 ex ->
               sc_consistent ex2 ->
               norace ex2) ->
  (forall ex2, sameP ex2 ex ->
               tso_consistent ex2 ->
               sc_consistent ex2).
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









