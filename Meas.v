From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
Require Import Posrat.

Import Monoid.Theory.

(* Linear combinations of elements of A *)

Definition Meas (A : eqType) := seq (posrat * A).


Section MeasOps.
  Context {A : eqType}.
  Definition measMass (d : Meas A) :=
    \big[padd/0%PR]_(p <- d) (p.1).
  Definition isDist (d : Meas A) :=
    (measMass d == 1).
  Definition isSubdist (d : Meas A) :=
    (measMass d <= 1).
  Definition measRed (d : Meas A) :=
    filter (fun p => p.1 != 0) d.
  Definition measSupport (d : Meas A) := map snd (measRed d).
  Definition indicator (x : A) := fun y => (if x == y then 1 else 0)%PR.
  Definition integ (d : Meas A) (f : A -> posrat) :=
    \big[padd/0%PR]_(p <- d) (p.1 * (f (p.2))).
  Definition measEquiv (e : posrat) (d1 d2 : Meas A)  := forall f, (forall x, f x <= 1)%PR ->
                                                                  pdist (integ d1 f) (integ d2 f) <= e.


End MeasOps.

Section MeasMonad.
  Context {A B : eqType}.

  Definition measRet (a : A) : Meas A := (1%PR,a) :: nil.

  Lemma isDist_ret : forall a, isDist (measRet a).
    intros.
    rewrite /isDist /measRet /measMass //=.
    rewrite big_cons big_nil.
    done.
  Qed.

  Definition measScale (r : posrat) (d : Meas B) : Meas B :=
    map (fun p => (r * p.1, p.2))%PR d.

  Definition measSum (ds : list (Meas B)) : Meas B :=
    flatten ds.

  Definition measJoin (d : Meas ([eqType of Meas B])) : Meas B :=
    measSum (map (fun p => measScale p.1 p.2) d).


  Definition measBind (d : Meas A) (f : A -> Meas B) : Meas B :=
    measJoin (map (fun p => (p.1, f (p.2))) d).

   
End MeasMonad.

  Definition meas_fmap {A C : eqType} (d : Meas A) (f : A -> C) : Meas C :=
    measBind d (fun x => measRet (f x)).


Lemma measJoin_cons {A : eqType} (d : Meas ([eqType of Meas A])) a :
  measJoin (a :: d) = (measScale (fst a) (snd a)) ++ (measJoin d).
  unfold measJoin.
  simpl.
  done.
Qed.

Lemma integ_nil {A : eqType} (f : A -> posrat) : integ nil f = 0.
  rewrite /integ.
  rewrite big_nil.
  done.
Qed.

Lemma integ_cons {A : eqType} (d1 : Meas A) a f : integ (a :: d1) f = (fst a) * f (snd a) + integ d1 f.
  unfold integ.
  rewrite big_cons.
  done.
Qed.

Lemma integ_app {A : eqType} (d1 d2 : Meas A) f : integ (d1 ++ d2) f = integ d1 f + integ d2 f.
  unfold integ.
  rewrite big_cat //=.
Qed.

Lemma integ_measScale {A : eqType} (d1 : Meas A) r f :
  integ (measScale r d1) f = r * (integ d1 f).
  unfold integ, measScale; rewrite //=.
  rewrite big_map //=.
  rewrite big_distrr //=.
  apply eq_big.
  intros; done.
  intros.
  rewrite pmulrA.
  done.
Qed.

Lemma integ_measJoin {A : eqType} (d : Meas ([eqType of Meas A])) (f : A -> posrat) :
  integ (measJoin d) f = integ d (fun d' => integ d' f).
  induction d.
  rewrite /measJoin /integ //= !big_nil.
  done.
  rewrite measJoin_cons.
  rewrite integ_app.
  rewrite integ_cons.
  rewrite IHd.
  rewrite integ_measScale.
  done.
Qed.

Lemma integ_measBind {A B : eqType} (d : Meas A) (df : A -> Meas B) f :
  integ (measBind d df) f = integ d (fun x => integ (df x) f).
  unfold measBind.
  rewrite integ_measJoin.
  induction d.
  unfold integ.
  rewrite big_map !big_nil.
  done.
  rewrite integ_cons.
  rewrite <- IHd.
  simpl.
  rewrite integ_cons.
  rewrite //=.
Qed.

Lemma measSupport_cons {A : eqType} (d : Meas A) (a : posrat * A) :
  measSupport (a :: d) = (if (fst a == 0) then measSupport d else (snd a) :: measSupport d).
  rewrite /measSupport //=.
  remember (a.1 == 0); symmetry in Heqb; destruct b.
  simpl.
  done.
  simpl.
  done.
Qed.

Lemma integ_cong_l {A : eqType} (d : Meas A) (f1 f2 : A -> posrat) e :
  (forall x, x \in (measSupport d) -> pdist (f1 x) (f2 x) <= e) ->
  pdist (integ d f1) (integ d f2) <= (measMass d * e).
  induction d.
  intros; rewrite !integ_nil /measMass big_nil.
  rewrite pmul0r.
  done.
  intro; rewrite !integ_cons.
  case (eqVneq a.1 0).
  intro Heq; rewrite Heq.
  rewrite !pmul0r !padd0r.
  rewrite /measMass.
  rewrite big_cons.
  rewrite Heq padd0r.
  apply IHd.
  intros; apply H.

  rewrite measSupport_cons.
  rewrite Heq; simpl.
  done.
  intros.
  rewrite /measMass.
  rewrite big_cons.
  rewrite pmulrDl.
  eapply ple_trans.
  apply pdist_add_lr.
  apply ple_add_lr.
  rewrite pdist_mul_l.
  apply ple_mul_l.
  apply H.
  rewrite measSupport_cons.
  rewrite (negbTE i).
  rewrite in_cons eq_refl orTb; done.
  apply IHd.
  intros; apply H.
  rewrite measSupport_cons (negbTE i) in_cons H0 orbT; done.
Qed.


Lemma integ_cong_l_exact {A : eqType} (d : Meas A) (f1 f2 : A -> posrat) :
  (forall x, x \in (measSupport d) -> f1 x = f2 x) ->
  integ d f1 = integ d f2.
  intros.
  apply/eqP; rewrite -pdist_le0.
  eapply ple_trans.
  apply integ_cong_l.
  intros.
  instantiate (1 := 0).
  rewrite pdist_le0.
  apply/eqP; apply H; done.
  rewrite pmulr0; done.
Qed.


Notation "'ret' x" := (@measRet  _ x) (at level 75).
Notation "x <- c1 ; c2" := (@measBind _ _ c1 (fun x => c2))
   (right associativity, at level 81, c1 at next level).                       



Notation "x ~~ y @ e" := (@measEquiv _ e x y) (at level 60).

Lemma integ_cong_r {A : eqType} (d1 d2 : Meas A) (e : posrat) (f : A -> posrat) : (forall x, f x <= 1) ->
  d1 ~~ d2 @ e -> pdist (integ d1 f) (integ d2 f) <= e.
  intros.
  apply H0.
  done.
Qed.

Require Import Setoid.

Lemma measEquiv_symm {A : eqType} : forall e (d1 d2 : Meas A),
    d1 ~~ d2 @ e -> d2 ~~ d1 @ e.
  intros; unfold measEquiv in *; intros. 
  rewrite pdist_symm.
  apply H.
  done.
Qed.

Lemma measEquiv_trans {A : eqType} : forall e1 e2 (d1 d2 d3 : Meas A) ,
    d1 ~~ d2 @ e1 -> d2 ~~ d3 @ e2 -> d1 ~~ d3 @ (e1 + e2).
  intros.
  unfold measEquiv in *; intros.
  eapply ple_trans.
  apply pdist_triangle.
  apply ple_add_lr.
  apply H; done.
  apply H0; done.
Qed.

Lemma measEquiv_0_trans {A : eqType} : forall (d1 d2 d3 : Meas A),
    d1 ~~ d2 @ 0 -> d2 ~~ d3 @ 0 -> d1 ~~ d3 @ 0.
  apply measEquiv_trans.
Qed.

Lemma measEquiv_refl {A : eqType} : forall (d : Meas A), d ~~ d @ 0.
  intros; unfold measEquiv; intros.
  rewrite ple_le0.
  rewrite pdist_eq0.
  done.
Qed.

Lemma measEquiv_sub {A : eqType} e1 e2 (d1 d2 : Meas A) :
  e1 <= e2 -> d1 ~~ d2 @ e1 -> d1 ~~ d2 @ e2. 
  intros.
  rewrite /measEquiv.
  intros.
  eapply ple_trans.
  apply H0.
  done.
  done.
Qed.

Add Parametric Relation (A : eqType) : (Meas A) (measEquiv 0)
    reflexivity proved by (measEquiv_refl)
    symmetry proved by (measEquiv_symm 0)
    transitivity proved by (measEquiv_0_trans)
    
                             as measEquiv0_rel.


(* Lemmas about monadic operations and ~~ *) 
  Lemma bindAssoc (A B C : eqType) : forall (c1 : Meas A) (c2 : A -> Meas B) (c3 : B -> Meas C),
    (x <- (y <- c1; c2 y); c3 x) ~~ (y <- c1; x <- c2 y; c3 x) @ 0.
    intros.
    unfold measEquiv; intros.
    repeat rewrite integ_measBind.
    rewrite pdist_le0.
    apply/eqP.
    apply integ_cong_l_exact; intros.
    repeat rewrite integ_measBind.
    apply integ_cong_l_exact; intros.
    done.
  Qed.

  Lemma bindRet {A B : eqType} (x : A) (c : A -> Meas B) :
    (z <- (ret x); c z) ~~ c x @ 0.
    intros; unfold measEquiv; intros.
    rewrite pdist_le0; apply/eqP.

    repeat rewrite integ_measBind.
    unfold measRet.
    rewrite integ_cons.
    rewrite integ_nil.
    simpl.
    rewrite paddr0.
    destruct (integ (c x) f).
    apply/eqP; rewrite /eq_op //=.
    by rewrite GRing.Theory.mul1r.
  Qed.

  Lemma bindRet_r {A : eqType} (c : Meas A) :
    (x <- c; ret x) ~~ c @ 0.
    unfold measEquiv; intros.
    rewrite integ_measBind.
    rewrite pdist_le0; apply/eqP.
    apply integ_cong_l_exact; intros.
    unfold measRet.
    rewrite integ_cons integ_nil //= paddr0.
    destruct (f x).
    apply/eqP; rewrite /eq_op //=.
    by rewrite GRing.Theory.mul1r.
  Qed.


Lemma measBind_cong_l {A : eqType} {d d' : Meas A} {e} :
  d ~~ d' @ e ->
  forall (B : eqType) (c : A -> Meas B),
  (forall x, isSubdist (c x)) ->
  measBind d c ~~ measBind d' c @ e.
  intros.
  unfold measEquiv; intros.
  repeat rewrite integ_measBind.
  apply H.
  intro; rewrite /integ.
  eapply ple_trans.
  eapply ple_sum.
  intros.
  instantiate (1 := fun x0 => x0.1 * 1); simpl.
  apply ple_mul_lr.
  apply ple_refl.
  apply H1.
  eapply ple_trans.
  apply ple_sum.
  intros.
  rewrite pmulr1 //=; apply ple_refl.
  apply H0.
Qed.

Lemma measBind_cong_r {A B : eqType} {d : Meas A} {c1 c2 : A -> Meas B} e :
  (forall x, x \in (measSupport d) -> c1 x ~~ c2 x @ e) ->
  (isSubdist d) ->
  measBind d c1 ~~ measBind d c2 @ e.
  intros.
  unfold measEquiv; intros; repeat rewrite integ_measBind.
  eapply ple_trans.
  eapply integ_cong_l.
  intros.
  apply H.
  done.
  done.
  eapply ple_trans.
  apply ple_mul_lr.
  apply H0.
  apply ple_refl.
  rewrite pmul1r; apply ple_refl.
Qed.

Lemma measBind_app {A B : eqType} (d1 d2 : Meas A) (c : A -> Meas B) :
  (p <- (d1 ++ d2); c p) ~~
                         ((p <- d1; c p) ++ (p <- d2; c p)) @ 0.
  rewrite /measBind /measJoin /meas_fmap !map_cat //=.
  rewrite /measSum flatten_cat.
  apply measEquiv_refl.
Qed.


Lemma measEquiv_cons_cong {A : eqType} {a b : (posrat * A)} (d1 d2 : Meas A) e :
  (fst a = fst b /\ snd a = snd b) ->
  d1 ~~ d2 @ e ->
  (a :: d1) ~~ (b :: d2) @ e.
  intros; unfold measEquiv; intros.
  rewrite !integ_cons.
  destruct H.
  rewrite H.
  rewrite H2.
  rewrite -pdist_add_l.
  apply H0; done.
Qed.

Lemma measEquiv_app_cong {A : eqType} {d1 d2 d3 d4 : Meas A} e1 e2 :
  d1 ~~ d2 @ e1 ->
  d3 ~~ d4 @ e2 ->
  (d1 ++ d3) ~~ (d2 ++ d4) @ (e1 + e2).
  unfold measEquiv; intros.
  rewrite /integ !big_cat //=.
  eapply ple_trans.
  apply pdist_add_lr.
  apply ple_add_lr.
  apply H; done.
  apply H0; done.
Qed.

Lemma measEquiv_app_cong_0 {A : eqType} {d1 d2 d3 d4 : Meas A} :
  d1 ~~ d2 @ 0 ->
  d3 ~~ d4 @ 0 ->
  (d1 ++ d3) ~~ (d2 ++ d4) @ 0.
  apply measEquiv_app_cong.
  Qed.

  

Lemma measBind_cons {A B : eqType} (d1 : Meas A) (c : A -> Meas B) a :
  (p <- a :: d1; c p) ~~ (measScale (fst a) (c (snd a)) ++ (p <- d1; c p)) @ 0.
  unfold measEquiv; intros.
  repeat rewrite integ_measBind.
  repeat rewrite integ_cons.
  rewrite pdist_le0.
  done.
Qed.

Lemma measScale_bind_l {A B : eqType} (d : Meas A) (f : A -> Meas B) (r : posrat) :
  measScale r (p <- d; f p) ~~
            (p <- (measScale r d); f p) @ 0.
  unfold measEquiv; intros.
  rewrite integ_measScale.
  repeat rewrite integ_measBind.
  rewrite integ_measScale.
  rewrite pdist_le0;
  done.
Qed.

Lemma measScale_cong {A : eqType} (d1 d2 : Meas A) (r : posrat) e :
  d1 ~~ d2 @ e ->
  (measScale r d1) ~~ (measScale r d2) @ (r * e).
  intros; unfold measEquiv; intros.
  repeat rewrite integ_measScale.
  rewrite pdist_mul_l.
  apply ple_mul_lr.
  apply ple_refl.
  apply H; done.
Qed.


Lemma measEquiv_zero_cons {A : eqType} (d : Meas A) (a : posrat * A) :
  fst a == 0 -> d ~~ (a :: d) @ 0.
  intros.
  unfold measEquiv, integ; intros.
  rewrite big_cons.
  rewrite (eqP H).
  rewrite pmul0r padd0r.
  rewrite pdist_le0;
  done.
Qed.

  
Lemma measSupport_app {A : eqType} (d1 d2 : Meas A) :
  measSupport (d1 ++ d2) = measSupport d1 ++ measSupport d2.
  unfold measSupport.
  unfold measRed.
  rewrite filter_cat.
  rewrite map_cat.
  done.
Qed.


Lemma measSupport_measScale {A : eqType} (d : Meas A) (r : posrat) :
   (r != 0) -> measSupport d = measSupport (measScale r d).
  intros.
  induction d.
  rewrite //=.
  rewrite //=.
  rewrite !measSupport_cons //=.
  destruct (eqVneq a.1 0).
  rewrite e.
  simpl.
  rewrite (pmulr0 r) //=.
  rewrite (negbTE i).
  have H2 := pmul0 r a.1.
  rewrite (negbTE H) in H2.
  rewrite (negbTE i) in H2.
  simpl in H2.
  rewrite -H2.
  rewrite IHd.
  done.
Qed.

Lemma measIndicator_in_support {A : eqType} (d : Meas A) : forall p, 
    ((integ d (fun x => if x == p then 1 else 0) != 0)) <->
    p \in (measSupport d).
  intros; split.
  intro.
  induction d.
  unfold integ in H.
  rewrite big_nil in H.
  done.
  rewrite integ_cons in H.
  rewrite measSupport_cons.
  destruct (eqVneq a.2 p).
  subst.
  destruct (eqVneq a.1 0).
  rewrite e //=.
  apply IHd.
  rewrite e in H.
  rewrite pmul0r in H.
  rewrite padd0r in H.
  simpl in *.
  done.
  
  rewrite (negbTE i).
  rewrite in_cons.
  rewrite eq_refl orTb; done.
  destruct (eqVneq a.1 0).
  rewrite e //=.
  apply IHd.
  rewrite e in H.
  rewrite pmul0r in H.
  rewrite padd0r in H.
  done.
  rewrite (negbTE i) in H.
  rewrite pmulr0 in H.
  rewrite padd0r in H.
  rewrite (negbTE i0).
  rewrite in_cons.
  rewrite IHd.
  apply orbT.
  done.

  intros.
  induction d.
  done.
  rewrite integ_cons.
  apply/contraT.
  intros.
  rewrite negbK in H0.
  have HP := padd0 (a.1 * (if a.2 == p then 1 else 0)) (integ d (fun x => if x == p then 1 else 0)).
  move/eqP: H0 => H0.
  rewrite H0 in HP.
  rewrite eq_refl in HP.
  move/andP: HP => [HP1 HP2].
  rewrite measSupport_cons in H.
  rewrite -pmul0 in HP1.
  move/orP: HP1 => HP1.
  destruct HP1.
  rewrite (eqP H1) in H.
  simpl in H.
  have HC := IHd H.
  rewrite (eqP HP2) in HC.
  done.
  destruct (eqVneq a.2 p).
  subst.
  rewrite eq_refl in H1.
  done.
  rewrite (negbTE i) in H1.
  rewrite (eqP HP2) in H0.
  rewrite (negbTE i) in H0.
  destruct (eqVneq a.1 0).
  rewrite e in H.
  simpl in H.
  have HC := IHd H.
  rewrite (eqP HP2) in HC.
  done.
  rewrite (negbTE i0) in H.
  move/orP: H => H.
  destruct H.
  rewrite (eqP H) in i.
  rewrite eq_refl in i.
  done.
  have HC := IHd H.
  rewrite (eqP HP2) in HC.
  done.
Qed.  

                           
Lemma measSupport_measEquiv {A : eqType} (d1 d2 : Meas A) : 
  d1 ~~ d2 @ 0 -> forall p, p \in (measSupport d1) -> p \in (measSupport d2). 
  intros.
  apply measIndicator_in_support.
  apply measIndicator_in_support in H0.
  have: forall x, (if x == p then 1 else 0) <= 1.
  intro; destruct (x == p); done.
  intro.
  have He := H (fun x => if x == p then 1 else 0) x.
  rewrite pdist_le0 in He.
  move/eqP: He => He.
  rewrite -He.
  done.
Qed.  


Lemma measEquiv_app_symm {A : eqType} (d1 d2 : Meas A) :
  (d1 ++ d2) ~~ (d2 ++ d1) @ 0.
  unfold measEquiv, integ; intros.
  rewrite !big_cat //=.
  rewrite paddrC.
  rewrite pdist_le0;
  done.
Qed.

Lemma measEquiv_rev {A : eqType} (d : Meas A) :
  d ~~ (rev d) @ 0.
  induction d.
  intro.
  rewrite integ_nil.
  done.
  have: a :: d = (a :: nil) ++ d.
  done.
  intro H; rewrite H; clear H.
  rewrite -(paddr0 0).
  eapply measEquiv_trans.
  apply measEquiv_app_symm.
  rewrite rev_cat.
  rewrite -(paddr0 0).
  apply measEquiv_app_cong.
  done.
  intro; intros; rewrite //=.
  rewrite /rev; simpl.
  rewrite pdist_le0; done.
Qed.

Definition unif {A : eqType} (xs : list A) : Meas A :=
  map (fun x => ((1 / posrat_of_nat (size xs)), x)) xs.

Lemma psumr_const {A} (xs : list A) (r : posrat) :
    \big[padd/0]_(p <- xs) r =  (posrat_of_nat (size xs)) * r.
  induction xs.
  rewrite big_nil.
  simpl.
  destruct r.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  rewrite GRing.mul0r.
  done.
  rewrite big_cons.
  rewrite IHxs.
  simpl.
  destruct r.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  rewrite intS intrD GRing.mulrDl //=.
  rewrite /intr //=.
  rewrite GRing.mul1r.
  done.
Qed.

Lemma unif_isDist {A : eqType} (xs : list A) : (size xs != 0%nat)-> isDist (unif xs).
  intro; rewrite /isDist /measMass /unif big_map //= psumr_const /eq_op //=; apply /eqP.
  rewrite GRing.mulrA.
  rewrite GRing.mulrC.
  rewrite GRing.mulr1.
  rewrite GRing.mulVr.
  done.
  rewrite GRing.unitfE.
  rewrite intr_eq0.
  done.
Qed.

Ltac drewr t :=
  match goal with
  | [ |- _ ~~ _ @ 0 ] => rewrite -(paddr0 0)
  | _ => idtac
           end;
  eapply measEquiv_trans; [ eapply t | idtac].

  Ltac dsimp := repeat (simpl; 
    match goal with
    | [ |- (_ <- ret _; _) ~~ _ @ _ ] => drewr @bindRet
    | [ |- _ ~~ (_ <- ret _; _) @ _ ] => apply measEquiv_symm; drewr @bindRet; apply measEquiv_symm
    | [ |- (_ <- (_ <- _; _); _) ~~ _ @ _ ] => drewr @bindAssoc
    | [ |- _ ~~ (_ <- (_ <- _; _); _) @ _ ] => apply measEquiv_symm; drewr @bindAssoc; apply measEquiv_symm
    | [ |- (_ <- _; ret _) ~~ _ @ _ ] => drewr @bindRet_r
    | [ |- _ ~~ (_ <- _; ret _) @ _ ] => apply measEquiv_symm; drewr @bindRet_r; apply measEquiv_symm
    | [ |- ?H ~~ ?H @ 0 ] => apply measEquiv_refl
                                            end; simpl; rewrite ?paddr0 ?padd0r).

  Ltac dsimp_in_l := etransitivity; eapply measBind_cong_r; intros; dsimp; apply measEquiv_refl.
  Ltac dsimp_in_r := symmetry; etransitivity; eapply measBind_cong_r; intros; dsimp; apply measEquiv_refl; symmetry.


Lemma measBind_in {A B : eqType} (d : Meas A) (d' : A -> Meas B) :
  forall y, y \in (measSupport (measBind d d')) <-> exists x,
      (x \in (measSupport d)) && (y \in (measSupport (d' x))).
  split; intros.
  rewrite /measSupport /measBind /measJoin /measRed /measSum in H.
  move/mapP: H => [p H].
  intro; subst.
  rewrite mem_filter in H; move/andP: H => [H0 H1].
  move/flattenP: H1; elim; intros; subst.
  rewrite /measScale in H.
  move/mapP: H; elim; intros; subst.
  move/mapP: H; elim; intros; subst.
  move/mapP: H1; elim; intros; subst.
  simpl in *.
  exists x.2.
  have HC := pmul0 x.1 x0.1.
  rewrite (negbTE H0) in HC.
  apply Bool.orb_false_elim in HC; destruct HC.
  apply/andP; split; rewrite /measSupport /measRed.
  apply/mapP.
  exists x.
  rewrite mem_filter.
  apply/andP; split.
  rewrite H2.
  done.
  done.
  done.
  apply/mapP; exists x0.
  rewrite mem_filter; apply/andP; split.
  rewrite H3.
  done.
  done.
  done.


  destruct H.
  move/andP: H => [H0 H1].
  rewrite /measSupport /measBind /measJoin /measRed /measSum.
  rewrite /measSupport /measBind /measJoin /measRed /measSum in H0.
  rewrite /measSupport /measBind /measJoin /measRed /measSum in H1.
  move/mapP: H0; elim; intros; subst.
  rewrite mem_filter in H; move/andP: H; elim; intros; subst.
  move/mapP: H1; elim; intros; subst.
  rewrite mem_filter in H1; move/andP: H1; elim; intros; subst.
  apply/mapP.

  exists (x0.1 * x.1, x.2).
  rewrite mem_filter; apply/andP; split.
  rewrite -pmul0.
  rewrite (negbTE H).
  rewrite (negbTE H1).
  done.
  apply/flattenP.
  simpl.
  exists [seq (x0.1 * p.1, p.2) | p <- d' x0.2].
  apply/mapP.
  simpl.
  exists (x0.1, d' x0.2).
  apply/mapP.
  exists x0.
  done.
  done.
  rewrite /measScale.
  simpl.
  done.
  apply/mapP.
  exists x.
  done.
  done.
  simpl; done.
Qed.

Lemma measBind_irr {A B : eqType} (d : Meas A) (h : A -> Meas B) (c : Meas B) :
  isDist d ->
  (forall x, h x ~~ c @ 0) ->
  (x <- d; h x) ~~ c @ 0.

  rewrite /isDist /measMass.
  intros.
  rewrite /measBind /measJoin /measEquiv /integ /measSum //=; intros.
  rewrite pdist_le0; apply /eqP.
  rewrite big_flatten //=.
  rewrite big_map //=.
  rewrite big_map //=.
  rewrite /measScale //=.
  etransitivity.
  apply eq_bigr; intros.
  rewrite big_map.
  simpl.
  etransitivity.
  apply eq_bigr.
  intro; rewrite -pmulrA; done.
  simpl.
  rewrite -big_distrr //=.
  simpl.
  etransitivity.
  apply eq_bigr.
  intros.
  have Heq := H0 i.2 f H1.
  rewrite pdist_le0 in Heq.
  move/eqP: Heq => Heq.
  rewrite /integ in Heq.
  rewrite Heq.
  apply pmulrC.
  simpl.
  etransitivity.
  apply eq_bigr.
  intros.
  rewrite big_distrl //=.
  simpl.
  rewrite exchange_big //=.
  apply eq_bigr.
  intros.
  rewrite -big_distrr //=.
  rewrite (eqP H).
  rewrite pmulr1.
  done.
Qed.

Lemma isSubdist_bind {A B : eqType} (d : Meas A) (f : A -> Meas B) :
  isSubdist d ->
  (forall x, isSubdist (f x)) ->
  isSubdist (measBind d f).
  rewrite /isSubdist /measMass /measBind /measJoin /measSum; intros.
  rewrite big_flatten //=.
  rewrite !big_map.
  rewrite /measScale //=.
  have:  \big[padd/0]_(j <- d) \big[padd/0]_(i <- [seq (j.1 * p.1, p.2) | p <- f j.2]) i.1 =
         \big[padd/0]_(j <- d) (j.1 * \big[padd/0]_(i <- f j.2) i.1). 
  apply eq_bigr; intros.
  rewrite big_map //=.
  rewrite big_distrr //=.
  intros.
  rewrite x; clear x.
  eapply ple_trans.
  apply ple_sum; intros.
  apply ple_mul_lr.
  apply ple_refl.
  apply H0.
  simpl.
  eapply ple_trans.
  apply ple_sum; intros; rewrite pmulr1; apply ple_refl.
  done.
Qed.

Lemma isSubdist_ret {A : eqType} (a : A) :
  isSubdist (ret a).
  rewrite /isSubdist /measMass /measRet.
  rewrite big_cons big_nil.
  done.
Qed.

Lemma isDist_isSubdist {A : eqType} (m : Meas A) :
  isDist m -> isSubdist m.
  rewrite /isDist /isSubdist.
  move/eqP; intro H; rewrite H; done.
Qed.

Lemma fmap_cong {A B : eqType} (d1 d2 : Meas A) ( f : A -> B) e :
  d1 ~~ d2 @ e ->
  meas_fmap d1 f ~~ meas_fmap d2 f @ e.
  rewrite /meas_fmap; intros; dsimp.
  apply measBind_cong_l.
  done.
  intros; apply isSubdist_ret.
Qed.  