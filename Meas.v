Add LoadPath "~/fcf/src".
Add LoadPath ".".
Require Import FCF.Rat.
Require Import FCF.Fold.
Require Import CpdtTactics.
Require Import FcfLems.
Require Import Ring.
Require Import List.
Require Import Coq.Classes.Equivalence.
Require Import Relation_Definitions.
Require Import Program.
Require Import FCF.StdNat.
Require Import Eqdep_dec.
Open Scope rat_scope.



Lemma sr_rat : @semi_ring_theory Rat 0 1 ratAdd ratMult eqRat.
  econstructor.
  intros; rewrite <- ratAdd_0_l; auto.
  crush.
  intros; rewrite ratAdd_comm; crush.
  intros; rewrite ratAdd_assoc; crush.
  intros; rewrite ratMult_1_l; crush.
  intros; rewrite ratMult_0_l; crush.
  intros; rewrite ratMult_comm; crush.
  intros; rewrite ratMult_assoc; crush.
  intros; rewrite ratMult_comm; rewrite ratMult_distrib; rewrite ratMult_comm; apply ratAdd_eqRat_compat; [crush | apply ratMult_comm; crush].
  Defined.


Add Ring ratring : sr_rat.

(* Linear combinations of elements of A *)
Definition Meas (A : Set) : Set := list (Rat * A).

Definition ratDisp (r : Rat) : nat * nat :=
  match r with
  | RatIntro n1 p =>
    match p with
    | exist _ n2 _ => (n1, n2)
    end
  end.

Definition MeasDisp {A} (d : Meas A) : list ((nat * nat) * A) :=
  map (fun p => (ratDisp (fst p), snd p)) d.

Section MeasOps.
  Context {A : Set}.
  Definition measMass (d : Meas A) := sumList (map fst d) (fun x => x).
  (* A measure is a distribution when it has total mass 1 and all elements have positive mass *)
  (* TODO: I can now remove the = 0 condition. *)
  Definition isDist (d : Meas A) :=
    (measMass d == 1).
  Definition measRed (d : Meas A) :=
    filter (fun p => negb (beqRat (fst p) 0)) d.
  Definition measSupport (d : Meas A) := map snd (measRed d).
  Definition integ (d : Meas A) (f : A -> Rat) :=
    sumList d (fun p => (fst p) * (f (snd p))).

  Definition measEquiv (d1 d2 : Meas A) := forall f, integ d1 f == integ d2 f.

End MeasOps.

Section MeasMonad.
  Context {A B : Set}.

  Definition measRet (a : A) : Meas A := (1, a) :: nil.
  Lemma isDist_ret : forall a, isDist (measRet a).
    intros.
    unfold isDist, measRet.
    unfold measMass.
    crush.
    unfold sumList; crush.
    ring.
  Qed.

  Definition measScale (r : Rat) (d : Meas B) :=
    map (fun p => (r * (fst p), snd p)) d.

  Definition measSum (ds : list (Meas B)) := concat ds.
  
  Definition measJoin (d : Meas (Meas B)) : Meas B :=
    measSum (map (fun p => measScale (fst p) (snd p)) d).

  Definition measBind (d : Meas A) (f : A -> Meas B) : Meas B :=
    measJoin (map (fun p => (fst p, f (snd p))) d).
   


End MeasMonad.

Notation "'ret' x" := (@measRet  _ x) (at level 75).
Notation "x <- c1 ; c2" := (@measBind _ _ c1 (fun x => c2))
   (right associativity, at level 81, c1 at next level).                       



Notation "x ~~ y" := (@measEquiv _ x y) (at level 60).


Require Import Setoid.

Lemma equiv_symm {A : Set} : forall (d1 d2 : Meas A),
    d1 ~~ d2 -> d2 ~~ d1.
  intros; unfold measEquiv in *; intros; crush.
Qed.

Lemma equiv_trans {A : Set} : forall (d1 d2 d3 : Meas A),
    d1 ~~ d2 -> d2 ~~ d3 -> d1 ~~ d3.
  intros; unfold measEquiv in *; intros; crush.
Qed.

Lemma measEquiv_refl {A : Set} : forall (d : Meas A), d ~~ d.
  intros; unfold measEquiv; intros; crush.
Qed.

Add Parametric Relation (A : Set) : (Meas A) (@measEquiv A)
   symmetry proved by equiv_symm
   transitivity proved by equiv_trans
   as meas_eq
.

(* Lemmas about monadic operations and ~~ *)

  Lemma bindAssoc {A B C : Set} : forall (c1 : Meas A) (c2 : A -> Meas B) (c3 : B -> Meas C),
    (x <- (y <- c1; c2 y); c3 x) ~~ (y <- c1; x <- c2 y; c3 x).
    intros.
    unfold measEquiv.
    intros.
    unfold measBind.
    unfold integ.
    unfold measJoin.
    unfold measSum.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    apply sumList_body_eq; intros.

    unfold measScale.
    simpl.
    rewrite sumList_map.
    rewrite sumList_map.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    apply sumList_body_eq; intros.
    rewrite sumList_map.
    rewrite sumList_map.
    simpl.
    apply sumList_body_eq; intros.
    ring.
Qed.

  Lemma bindRet {A B : Set} (x : A) (c : A -> Meas B) :
    (z <- (ret x); c z) ~~ c x.
    intros; unfold measEquiv; intros; simpl.
    unfold integ.
    unfold measBind.
    unfold measJoin.
    unfold measSum.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    unfold measRet.
    simpl.
    rewrite sumList_cons.
    rewrite sumList_nil.
    unfold measScale; simpl.
    rewrite sumList_map.
    rewrite <- ratAdd_0_r.
    apply sumList_body_eq; intros.
    simpl.
    ring.
  Qed.

  Lemma bindRet_r {A : Set} (c : Meas A) :
    (x <- c; ret x) ~~ c.
    unfold measBind.
    unfold measJoin.
    unfold measSum.
    simpl.
    rewrite map_map.
    simpl.
    induction c.
    crush.
    unfold measEquiv; crush.
    simpl.
    unfold measEquiv; intros.
    unfold integ.
    unfold measEquiv, integ in IHc.
    repeat rewrite sumList_cons.
    symmetry in IHc.
    rewrite (IHc _).
    simpl.
    ring.
  Qed.

Ltac in_sumList_l := eapply eqRat_trans; [ apply sumList_body_eq; intros; simpl | idtac] .

Lemma measBind_cong_l {A B : Set} {d d' : Meas A} {c : A -> Meas B} :
  d ~~ d' ->
  measBind d c ~~ measBind d' c.
  intros.
  unfold measBind, measEquiv in *.
  unfold measJoin.
  unfold measSum.
  intros.

  rewrite map_map.
  rewrite map_map.
  unfold measScale.
  unfold integ in H.
  unfold integ.
  rewrite sumList_concat.
  rewrite sumList_concat.
  rewrite sumList_map.
  rewrite sumList_map.
  simpl.
  in_sumList_l.
  apply sumList_map.
  simpl.
  eapply eqRat_trans.
  in_sumList_l.
  in_sumList_l.
  apply ratMult_assoc.
  apply sumList_factor_constant_l.
  apply (H (fun a => sumList (c a) (fun a0 => fst a0 * f (snd a0)))).
  apply sumList_body_eq.
  intros.
  rewrite sumList_map.
  simpl.
  symmetry.
  in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  crush.
Qed.

Lemma measBind_cong_r {A B : Set} {d : Meas A} {c c' : A -> Meas B} :
  (forall x, In x (measSupport d) -> c x ~~ c' x) ->
  measBind d c ~~ measBind d c'.
  intros.
  unfold measBind, measEquiv in *.
  unfold measJoin; unfold measSum; intros.
  rewrite map_map.
  unfold integ; intros.
  rewrite map_map.
  rewrite sumList_concat.
  rewrite sumList_concat.
  repeat rewrite sumList_map.
  apply sumList_body_eq; intros.
  simpl.
  unfold measScale; simpl.
  repeat rewrite sumList_map.
  simpl.
  unfold integ in H.
  destruct a; simpl.
  in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  remember (beqRat r 0) as b; destruct b.
  assert (r == 0).
  unfold eqRat; crush.
  symmetry.
  etransitivity.
  apply sumList_body_eq; intros; apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  repeat rewrite H1.
  ring.
  rewrite H.
  symmetry; in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  crush.
  unfold measSupport.
  unfold measRed.
  apply in_map_iff; intros.
  exists (r,a).
  crush.
  apply filter_In.
  crush.
  rewrite <- Heqb.
  crush.
Qed.  

Lemma measBind_equiv_ret {A : Set} {H : forall (x y : A), {x = y} + {x <> y}} (x y : A) :
  (ret x) ~~ (ret y) -> x = y.
  intros.
  destruct (H x y).
  auto.

  unfold measEquiv in H0.
  unfold measRet in H.
  unfold integ in H; simpl in H.
  unfold sumList in H; simpl in H.
  pose proof (H0 (fun a => if H a x then 1 else 0)).
  unfold integ in H1.
  unfold sumList in H1; unfold measRet in H1; simpl in *.
  repeat rewrite <- ratAdd_0_l in H1.
  repeat rewrite ratMult_1_l in H1.
  destruct (H x x); destruct (H y x); crush.
Qed.

(*
Lemma bind_symm {A B C: Set} (d11 d12 : Meas A) (d21 d22 : Meas B) (c1 c2 : A -> B -> Meas C) :
  (forall x y, c1 x y ~~ c2 x y) -> 
  d11 ~~ d12 ->
  d21 ~~ d22 ->
  (x <- d11; y <- d21; c1 x y) ~~
  (y <- d22; x <- d12; c2 x y).
  admit.
Admitted.
*)

  
(* Lemmas about distributions *)

Lemma join_measmass {A : Set} (d : Meas (Meas A)) : measMass d == 1 -> (forall p, In p (map snd d) -> measMass p == 1) -> measMass (measJoin d) == 1.
  intros.
  unfold measJoin.
  unfold measSum.
  unfold measMass.
  rewrite sumList_map.
  rewrite sumList_concat.
  rewrite sumList_map.
  unfold measMass in H.
  rewrite sumList_map in H.
  rewrite <- H.
  apply sumList_body_eq.
  intros.
  simpl.
  unfold measScale; simpl.
  rewrite sumList_map.
  simpl.
  rewrite sumList_factor_constant_l.
  unfold measMass in H0.
  cut (sumList (snd a) fst == 1).
  intro H2; rewrite H2; ring.
  rewrite <- H0.
  rewrite sumList_map.
  reflexivity.
  apply in_map.
  crush.
Qed.


Lemma join_in {A : Set} (d : Meas (Meas A)) :
  forall r, In r (map fst (measJoin d)) ->
            exists p r',
              In p d /\ In r' (map fst (snd p)) /\ r == (fst p) * r'.
  induction d.
  intros.
  unfold measJoin in H; simpl in H; crush.
  intros.
  unfold measJoin in H.
  simpl in H.
  rewrite map_app in H.
  apply in_app_or in H.
  destruct H.
  exists a.
  destruct a; simpl in H.
  unfold measScale in H.
  rewrite map_map in H.
  simpl in H.
  simpl.
  apply in_map_iff in H.
  destruct H.
  exists (fst x).
  crush.
  apply in_map; crush.

  destruct (IHd r H).
  destruct H0.
  exists x,x0.
  crush.
Qed.


Lemma join_neq_0 {A : Set} (d : Meas (Meas A)) : (forall r, In r (map fst d) -> ~ (r == 0)) /\
                                                 (forall p r, In p (map snd d) -> In r (map fst p) -> ~ (r == 0)) ->
                                                 (forall r, In r (map fst (measJoin d)) -> ~ (r == 0)).
  intros.
  apply join_in in H0.
  repeat destruct H0.
  destruct H1.
  rewrite H2.
  apply ratMult_nz.
  destruct H.
  split.
  apply H.
  apply in_map; auto.
  eapply H3.
  apply in_map.
  apply H0.
  auto.
Qed.
  
Lemma isDist_Join {A : Set} (d : Meas (Meas A)) : isDist d -> (forall p, In p d -> isDist (snd p)) -> isDist  (measJoin d).
  intros.
  unfold isDist in H.
  unfold isDist.
  apply join_measmass.
  crush.
  intros.
  unfold isDist in H0.
  apply in_map_iff in H1; crush.
Qed.

Lemma isDist_Bind {A B : Set} (d : Meas A) (f : A -> Meas B) : isDist d -> (forall a, isDist (f a)) -> isDist (measBind d f).
  intros.
  unfold measBind.
  apply isDist_Join.
  unfold isDist.
  unfold measMass.

  rewrite map_map.
  simpl.
  apply H.
  intros.
  apply in_map_iff in H1; crush.
Qed.


  Lemma in_concat_iff {A : Set} : forall (x : A) (ls : list (list A)),
      In x (concat ls) <-> exists l, In l ls /\ In x l.
    intros.
    split.
    induction ls.
    intros.
    inversion H.
    intros.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    exists a.
    crush.
    destruct (IHls H).
    exists x0.
    crush.

    intros.
    destruct H.
    induction ls.
    crush.
    simpl.
    destruct H.
    apply in_app_iff.
    crush.
  Qed.

Lemma measBind_in {A B : Set} (d : Meas A) (d' : A -> Meas B) :
  forall y, In y (measSupport (measBind d d')) <-> exists x,
      In x (measSupport d) /\ In y (measSupport (d' x)).
  split; intros.
  unfold measSupport, measBind, measRed, measJoin in H.
  rewrite map_map in H; simpl in H.
  unfold measSum in H.
  apply in_map_iff in H; crush.
  apply filter_In in H1; crush.
  apply in_concat_iff in H; crush.
  apply in_map_iff in H1; crush.
  unfold measScale in H2.
  apply in_map_iff in H2; crush.

  destruct (eq_Rat_dec (fst x1) 0).
  assert ((fst x1) * (fst x0) == 0).
  rewrite e; ring.
  rewrite H in H0.
  crush.
  destruct (eq_Rat_dec (fst x0) 0).
  assert (fst x1 * fst x0 == 0). rewrite e; ring.
  rewrite H in H0; crush.


  exists (snd x1).
  split.
  unfold measSupport.
  unfold measRed.
  apply in_map_iff.
  exists x1.
  crush.
  apply filter_In.
  crush.
  unfold measSupport.
  unfold measRed.
  apply in_map_iff; exists x0.
  crush.
  apply filter_In.
  crush.

  destruct H.
  unfold measBind, measSupport.
  crush.
  unfold measSupport in *.
  apply in_map_iff in H0; crush.
  apply in_map_iff in H1; crush.
  unfold measRed in *.
  apply filter_In in H2; crush.
  apply filter_In in H1; crush.
  apply in_map_iff.

  exists (fst x0 * fst x, snd x).
  crush.
  apply filter_In.
  crush.
  unfold measJoin.
  unfold measSum.
  rewrite map_map.
  unfold measScale.
  simpl.
  apply in_concat_iff.
  exists (measScale (fst x0) (d' (snd x0))).
  crush.
  apply in_map_iff.
  exists x0.
  crush.
  apply in_map_iff.
  exists x.
  crush.

  rewrite Bool.negb_true_iff in *.
  assert (forall n, n = false <-> n <> true).
  destruct n; crush.
  apply H1.
  apply ratMult_nz.
  crush.
Qed.


  Definition fmap {A B : Set} (d : Meas A) (f : A -> B) : Meas B := p <- d; ret (f p).

Lemma meas_fmap_cong {A B : Set} {d1 d2 : Meas A} {f : A -> B} :
  d1 ~~ d2 -> fmap d1 f ~~ fmap d2 f.
  intros.
  unfold fmap.
  apply (measBind_cong_l H).
Qed.

Definition measCong {A B : Set} (f : Meas A -> Meas B) :=
  forall d1 d2,
    d1 ~~ d2 -> f d1 ~~ f d2.
        
Definition joinDistrib {A B : Set} (f : Meas A -> Meas B) :=
  forall mu,
    f (p <- mu; p) ~~ (p <- (fmap mu f); p).


Lemma measBind_cons {A B : Set} (d : Meas A) (c : A -> Meas B) (a : Rat * A) :
  (p <- (a :: d); c p) ~~ ((p <- d; c p) ++ (p <- (a :: nil); c p)).
  unfold measBind.
  simpl.
  unfold measJoin.
  simpl.
  unfold measEquiv; intros.
  unfold integ.
  repeat rewrite Fold.sumList_app.
  rewrite ratAdd_comm.
  apply ratAdd_eqRat_compat; crush.
  unfold Fold.sumList; simpl.
  rewrite <- ratAdd_0_r.
  crush.
Qed.

Lemma measBind_app {A B : Set} (d1 d2 : Meas A) (c : A -> Meas B) :
  (p <- (d1 ++ d2); c p) ~~
                         ((p <- d1; c p) ++ (p <- d2; c p)).
  unfold measBind.
  unfold measJoin.
  rewrite map_app.
  rewrite map_app.
  unfold measSum.
  rewrite concat_app.
  unfold measEquiv; intros; crush.
Qed.

Lemma measEquiv_cons_cong {A : Set} {a b : (Rat * A)} (d1 d2 : Meas A) :
  (fst a == fst b /\ snd a = snd b) ->
  d1 ~~ d2 ->
  (a :: d1) ~~ (b :: d2).
  unfold measEquiv; unfold integ; intros.
  repeat rewrite Fold.sumList_cons.
  destruct H.
  rewrite H.
  rewrite H1.
  rewrite H0.
  crush.
Qed.

Lemma measEquiv_app_cong {A : Set} {d1 d2 d3 d4 : Meas A} :
  d1 ~~ d2 ->
  d3 ~~ d4 ->
  (d1 ++ d3) ~~ (d2 ++ d4).
  unfold measEquiv; unfold integ; intros.
  repeat rewrite Fold.sumList_app.
  rewrite H.
  rewrite H0.
  crush.
Qed.

Lemma measScale_bind_l {A B : Set} (d : Meas A) (f : A -> Meas B) (r : Rat) :
  measScale r (p <- d; f p) ~~
            (p <- (measScale r d); f p).
  unfold measEquiv, measBind, measScale; intros; simpl.
  unfold integ.
  unfold measJoin.
  unfold measSum.
  rewrite concat_map.
  rewrite map_map.
  repeat rewrite sumList_concat.
  repeat rewrite Fold.sumList_map.
  apply Fold.sumList_body_eq; intros.
  unfold measScale; simpl.
  repeat rewrite Fold.sumList_map.
  apply Fold.sumList_body_eq; intros.
  simpl.
  ring.
Qed.

Lemma measScale_bind_r {A B : Set} (d : Meas A) (f : A -> Meas B) (r : Rat) :
  measScale r (p <- d; f p) ~~
            (p <- d; measScale r (f p)).
  unfold measEquiv, measBind, measScale; intros; simpl.
  unfold integ.
  unfold measJoin.
  unfold measSum.
  rewrite concat_map.
  rewrite map_map.
  repeat rewrite sumList_concat.
  repeat rewrite Fold.sumList_map.
  apply Fold.sumList_body_eq; intros.
  unfold measScale; simpl.
  repeat rewrite Fold.sumList_map.
  apply Fold.sumList_body_eq; intros.
  simpl.
  ring.
Qed.  

Lemma measScale_cong {A : Set} (d1 d2 : Meas A) (r : Rat) :
  d1 ~~ d2 ->
  (measScale r d1) ~~ (measScale r d2).
  intros; unfold measEquiv, integ in *; intros.
  unfold measScale.
  repeat rewrite Fold.sumList_map.
  simpl.
  etransitivity.
  apply Fold.sumList_body_eq.
  intros.
  instantiate (1 := (fun a => r * (fst a * f (snd a)))).
  simpl.
  ring.
  rewrite Fold.sumList_factor_constant_l.
  rewrite H.
  rewrite <- Fold.sumList_factor_constant_l.
  apply Fold.sumList_body_eq; intros; ring.
Qed.

(* TODO: tactics for simplifying distributions. *)


Lemma measEquiv_zero_cons {A : Set} (d : Meas A) (a : Rat * A) :
  fst a == 0 -> d ~~ (a :: d).
  intros.
  unfold measEquiv, integ; intros.
  rewrite sumList_cons.
  rewrite H.
  ring.
Qed.

Lemma measSupport_app {A : Set} (d1 d2 : Meas A) :
  measSupport (d1 ++ d2) = measSupport d1 ++ measSupport d2.
  unfold measSupport.
  unfold measRed.
  rewrite filter_app.
  rewrite map_app.
  crush.
Qed.

Lemma measSupport_cons {A : Set} (d : Meas A) (a : Rat * A) :
  measSupport (a :: d) = (if beqRat (fst a) 0 then measSupport d else (snd a) :: measSupport d).
  unfold measSupport.
  crush.
  destruct (beqRat a0 0); crush.
Qed.

Lemma measSupport_measScale {A : Set} (d : Meas A) (r : Rat) :
  ~ (r == 0) -> measSupport d = measSupport (measScale r d).
  intros.
  induction d.
  crush.
  simpl.
  repeat rewrite measSupport_cons.
  simpl.
  remember (beqRat (fst a) 0).
  destruct b.
  assert (fst a == 0). unfold eqRat; crush.
  assert (r * fst a == 0).
  rewrite H0.
  ring.
  rewrite H1.
  crush.

  assert (~ (r * fst a == 0)).
  apply ratMult_nz.
  crush.
  remember (beqRat (r * fst a) 0) as b; destruct b.
  crush.
  crush.
Qed.

Lemma measIndicator_in_support {A : Set} (H : forall x y : A, {x = y} + {x <> y}) (d : Meas A) : forall p, 
    (~ (integ d (fun x => if H x p then 1 else 0) == 0)) <->
    In p (measSupport d).
  split.
  intros.
  induction d.
  unfold integ in H0; rewrite sumList_nil in H0.
  crush.
  unfold integ in *.
  rewrite sumList_cons in H0.
  destruct (H (snd a) p).
  destruct (eq_Rat_dec (fst a) 0).
  rewrite e0 in H0.
  rewrite measSupport_cons.
  rewrite e0.
  apply IHd.

  rewrite ratMult_0_l in H0.
  rewrite <- ratAdd_0_l in H0.
  crush.

  rewrite measSupport_cons.
  rewrite (Bool.not_true_is_false _ n).
  subst.
  crush.

  rewrite measSupport_cons.
  destruct (eq_Rat_dec (fst a) 0).
  rewrite e.
  apply IHd.
  rewrite ratMult_0_r in H0.
  rewrite <- ratAdd_0_l in H0.
  crush.
  rewrite (Bool.not_true_is_false _ n0).
  right;
  apply IHd.
  rewrite ratMult_0_r in H0.
  rewrite <- ratAdd_0_l in H0.
  crush.

  intros.
  induction d.
  crush.
  unfold integ; simpl in *.
  rewrite sumList_cons.
  rewrite measSupport_cons in H0.
  destruct (H (snd a) p).
  subst.
  destruct (eq_Rat_dec (fst a) 0).
  rewrite e.
  rewrite ratMult_0_l.
  rewrite <- ratAdd_0_l.
  apply IHd.
  rewrite e in H0.
  crush.

  apply ratAdd_nz.
  left.
  rewrite ratMult_1_r; crush.
  destruct (eq_Rat_dec (fst a) 0).
  rewrite e.
  rewrite e in H0.
  rewrite ratMult_0_r.
  rewrite <- ratAdd_0_l.
  apply IHd; crush.
  apply ratAdd_nz.
  right; apply IHd.
  rewrite (Bool.not_true_is_false _ n0) in H0.
  destruct H0.
  crush.
  crush.
Qed.
  
                           
Lemma measSupport_measEquiv {A : Set} (H : forall x y : A, {x = y} + {x <> y}) (d1 d2 : Meas A) :
  d1 ~~ d2 -> forall p, In p (measSupport d1) -> In p (measSupport d2). 
  intros.
  apply (measIndicator_in_support H) in H1.
  apply (measIndicator_in_support H).
  intro.
  rewrite (H0 (fun x => if H x p then 1 else 0)) in H1.
  crush.
Qed.  


Lemma sumList_zip {A : Set} (l l' : list A) (f f' : A -> Rat) :
  length l = length l' ->
  (forall p, In p (zip l l') -> f (fst p) == f' (snd p)) ->
  sumList l f == sumList l' f'.
  revert l'.
  induction l.
  induction l'.
  crush.
  unfold sumList; crush.
  crush.
  intros.
  induction l'.
  crush.
  assert (sumList l f == sumList l' f').
  apply IHl.
  crush.
  intros.
  simpl in H0.
  apply H0; crush.
  repeat rewrite sumList_cons.
  rewrite H1.
  pose proof (H0 _ (or_introl (eq_refl (a, a0)))); simpl in *.
  rewrite H2.
  crush.
Qed.

Lemma measEquiv_app_symm {A : Set} (d1 d2 : Meas A) :
  (d1 ++ d2) ~~ (d2 ++ d1).
  unfold measEquiv, integ; intros.
  repeat rewrite sumList_app.
  ring.
Qed.

Lemma measEquiv_rev {A : Set} (d : Meas A) :
  d ~~ (rev d).
  induction d.
  unfold measEquiv; crush.
  simpl.
  assert (a :: d = [a] ++ d).
  crush.
  rewrite H.
  rewrite measEquiv_app_symm.
  apply measEquiv_app_cong.
  crush.
  unfold measEquiv; crush.
Qed.

Lemma measBind_zip {A B : Set} {d d' : Meas A} {c c' : A -> Meas B} :
  length d = length d' ->
  (forall p, In p (zip d d') -> fst (fst p) == fst (snd p) /\ c (snd (fst p)) ~~ c' (snd (snd p))) ->
  measBind d c ~~ measBind d' c'.

  intros.
  unfold measBind, measJoin, measEquiv, measSum, integ; intros.
  repeat rewrite sumList_concat.
  repeat rewrite sumList_map.
  eapply sumList_zip.
  crush.
  intros.
  simpl.
  destruct (H0 _ H1).
  unfold measScale.
  repeat rewrite sumList_map.
  simpl.
  etransitivity.
  apply sumList_body_eq; intros; apply ratMult_assoc.
  symmetry; etransitivity.
  apply sumList_body_eq; intros; apply ratMult_assoc.
  repeat rewrite sumList_factor_constant_l.
  apply ratMult_eqRat_compat.
  crush.
  symmetry; apply (H3 f).
Qed.


(*
Global Instance nz_length_app {A} (l1 l2 : list A) {H1 : nz (length l1)} {H2 : nz (length l2)} : nz (length (l1 ++ l2)).
destruct H1.
destruct H2.
constructor.
rewrite app_length.
crush.
Defined.

Global Instance nz_allnatslt_length (n : nat) {H1 : nz n} : nz (length (allNatsLt n)).
destruct n.
destruct H1; crush.
simpl.
rewrite app_length.
crush.
constructor.
crush.
Defined.
*)

(* uniformity *)


(* Proof irrelevent inverses *)

Definition natpos (n : nat) :=
  match n with | 0 => false | _ => true end = true.


Global Instance natpos_nz (n : nat) {H : natpos n} : nz n.
destruct n; crush.
Defined.

Definition natInverse (n : nat) {H : natpos n} : Rat.
  apply RatIntro.
  apply 1%nat.
  eapply exist.
  apply natpos_nz.
  apply H.
Defined.

Notation "1 // n" := (match n with | 0 => 0 | S m => @natInverse (S m) eq_refl end) (at level 60).  

Lemma natpos_irrel {n : nat} (H1 H2 : natpos n) : H1 = H2.
  destruct n; crush.
  unfold natpos in *.
  apply eq_proofs_unicity.
  decide equality.
Qed.

Definition unif {A : Set} (xs : list A) : Meas A :=
  match (length xs) with
  | 0 => nil
  | S n => 
    map (fun x => (1 // (S n), x)) xs
        end.

Definition unifNats (n : nat) : Meas (nat) := unif (allNatsLt n).


Lemma unif_cons {A : Set} (l1 : list A) (a : A) :
  unif (a :: l1) = ((1 // S (length l1), a) :: (map (fun p => (1 // (S (length l1)), snd p)) (unif l1))).
  unfold unif; simpl.
  destruct l1.
  crush.
  simpl.
  rewrite map_map.
  simpl.
  crush.
Qed.


Lemma unif_app {A : Set} (l1 l2 : list A) :
  unif (l1 ++ l2) = map (fun p => (1 // length (l1 ++ l2), snd p)) (unif l1 ++ unif l2).
  unfold unif.
  destruct l1; destruct l2; simpl.
  crush.
  rewrite map_map; crush.
  repeat rewrite app_nil_r; simpl.
  rewrite map_map; simpl.
  crush.
  repeat rewrite map_app.
  repeat rewrite map_map.
  simpl.
  repeat rewrite map_map.
  simpl.
  crush.
Qed.

Lemma unifNats_in (n : nat) : forall p,
    In p (measSupport (unifNats n)) -> p < n.
  induction n.
  crush.
  crush.
  unfold unifNats in H.
  simpl in H.
  rewrite unif_app in H.
  unfold measSupport in H.
  unfold measRed in H.
  rewrite map_app in H; crush.
  rewrite filter_app in H.
  simpl in H.
  rewrite map_app in H.
  apply in_app_iff in H; crush.
  assert (In p (measSupport (unifNats n))).
  apply in_map_iff in H0; crush.
  apply filter_In in H1; crush.
  apply in_map_iff in H; crush.
  apply in_map_iff; exists x0.
  crush.
  unfold measRed.
  apply filter_In; crush.
  clear H0.
  clear IHn.
  destruct n.
  crush.
  simpl in H2.
  rewrite unif_app in H2.
  rewrite map_app in H2; simpl in *.
  destruct x0; apply in_app_iff in H2; crush.
  apply in_map_iff in H; crush.
  unfold natInverse.
  rewrite app_length.
  simpl.
  remember (length (allNatsLt n) + 1)%nat.
  destruct n0.
  destruct (length (allNatsLt n)); crush.
  crush.
  unfold natInverse; rewrite app_length.
  simpl.
  remember (length (allNatsLt n0) + 1)%nat.
  destruct n.
  destruct (length (allNatsLt n0)); crush.
  destruct (length (allNatsLt n0) + 1)%nat; crush.
  apply Nat.lt_lt_succ_r.
  crush.
  apply in_map_iff in H0; crush.
  destruct x; simpl.
  remember (negb (beqRat (1 // length (allNatsLt n ++ [n])) 0)).
  destruct b.
  simpl in H1.
  crush.
  crush.
Qed.


  Ltac dsimp := repeat (simpl; 
    match goal with
    | [ |- context[_ <- ret _; _] ] => rewrite bindRet
    | [ |- context[_ <- (_ <- _; _); _] ] => rewrite bindAssoc
    | [ |- context[_ <- _; ret _] ] => rewrite bindRet_r
    | [ |- ?H ~~ ?H ] => apply measEquiv_refl
                                            end; simpl).

  Ltac dsimp_in_l := etransitivity; eapply measBind_cong_r; intros; dsimp; apply measEquiv_refl.
  Ltac dsimp_in_r := symmetry; etransitivity; eapply measBind_cong_r; intros; dsimp; apply measEquiv_refl; symmetry.

