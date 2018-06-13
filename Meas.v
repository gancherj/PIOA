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
  Definition isDist (d : Meas A) :=
    (measMass d == 1) /\
    (forall r, In r (map fst d) -> ~ (r == 0)).
  Definition measSupport (d : Meas A) := map snd d.
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
    split.

    unfold measMass; unfold sumList; crush; ring.
    intros.
    inversion H; crush.
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
  rewrite H.
  symmetry; in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  crush.
  unfold measSupport.
  apply in_map_iff.
  exists (r,a); crush.
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
  unfold isDist in H; destruct H.
  unfold isDist.
  split.
  apply join_measmass.
  crush.
  intros.
  apply in_map_iff in H2.
  
  destruct H2.
  destruct H2.
  destruct (H0 x).
  crush.
  rewrite <- H2; crush.

  apply join_neq_0.
  split.
  apply H1.
  intros.
  apply in_map_iff in H2.
  destruct H2.
  destruct H2; subst.
  destruct (H0 _ H4).
  apply H5.
  crush.
Qed.

Lemma isDist_Bind {A B : Set} (d : Meas A) (f : A -> Meas B) : isDist d -> (forall a, isDist (f a)) -> isDist (measBind d f).
  intros.
  unfold measBind.
  apply isDist_Join.
  unfold isDist.
  split.
  unfold measMass.
  rewrite map_map.
  simpl.
  destruct H.
  apply H.
  destruct H.
  intros.
  apply H1.
  rewrite map_map in H2.
  simpl in H2.
  auto.

  intros.
  apply in_map_iff in H1.
  destruct H1.
  destruct H1; subst.
  simpl.
  apply H0.
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
  forall y, In y (measSupport (measBind d d')) -> exists x,
      In x (measSupport d) /\ In y (measSupport (d' x)).
  unfold measBind, measSupport, measJoin. 
  unfold measSum.
  rewrite map_map.
  simpl.
  intros.
  apply in_map_iff in H.
  destruct H.
  destruct H.
  apply in_concat_iff in H0.
  destruct H0.
  destruct H0.
  apply in_map_iff in H0.
  destruct H0.
  exists (snd x1).
  split.
  apply in_map_iff.
  exists x1; crush.
  subst.
  crush.
  apply in_map_iff.
  unfold measScale in H1.
  apply in_map_iff in H1.
  destruct H1.
  destruct H.
  subst.
  simpl.
  exists x0; crush.
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


Definition unif {A : Set} (xs : list A) `{StdNat.nz (length xs)} : Meas A :=
  map (fun x => (1 / (length xs), x)) xs.


Definition unifNats (n : nat) `{StdNat.nz n} : Meas (nat).
  eapply (@unif _ (allNatsLt n)).
  rewrite allNatsLt_length.
  auto.
Defined.