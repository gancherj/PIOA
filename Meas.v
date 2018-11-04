
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
Require Import PIOA.Posrat PIOA.Premeas.

Record Meas (A : choiceType) :=
  {
    _pmeas :> PMeas A;
    _ : canonical_keys _pmeas && nubbed _pmeas
                       }.

Arguments _pmeas [A].

Canonical Structure meassub (A : choiceType) := [subType for (@_pmeas A)].
Definition measEqmix (A : choiceType) := [eqMixin of Meas A by <:].
Canonical Structure measEqtype (A : choiceType) := EqType (Meas A) (measEqmix A).
Definition measChoicemix (A : choiceType) := [choiceMixin of (Meas A) by <: ].
Canonical measChoicetype A := ChoiceType (Meas A) (measChoicemix A).

Definition mkMeas {A : choiceType} (d : PMeas A) : Meas A.
  econstructor.
  apply/andP; split.
  instantiate (1 := sort_keys (measUndup d)).
  apply canonical_sort_keys.
  apply nubbed_sort_keys.
  apply measUndup_nubbed.
Defined.

Lemma integ_mkMeas {A : choiceType} (d : PMeas A) f :
  integ (mkMeas d) f = integ d f.
  have: integ (mkMeas d) f = integ (measUndup d) f.
  remember (mkMeas d) as c.
  destruct c as [cd h1 h2].
  rewrite //=.
  injection Heqc.
  move => ->.
  rewrite /integ.
  eapply eq_big_perm.
  have: measUndup d = undup (measUndup d).
  symmetry; apply undup_id.
  apply uniq_proj_uniq.
  have: nubbed (measUndup d).
  apply measUndup_nubbed.
  move/andP; elim; done.
  move => heq.
  rewrite {2}heq.
  rewrite SortKeys.perm; done.
  move => ->.
  rewrite -measUndupE //=.
Qed.

Lemma integ_meas {A : choiceType} (d : Meas A) f :
  integ d f = integ (_pmeas d) f.
  done.
Qed.

Definition MeasP {A : choiceType} (d1 d2 : Meas A) :
  (d1 = d2) <-> (forall f, integ d1 f = integ d2 f).
  destruct d1, d2; rewrite //=.
  split; intros.
  apply nubbed_sortedP; rewrite //=.
  injection H; rewrite //=.
  have: _pmeas0 = _pmeas1.
  apply nubbed_sortedP; rewrite //=.
  elim (andP i); done.
  elim (andP i0); done.
  elim (andP i); done.
  elim (andP i0); done.
  intros.
  injection H; move => ->; done.
  intros; elim (andP i); done.
  intros; elim (andP i0); done.
  intros; elim (andP i); done.
  intros; elim (andP i0); done.
  injection H; done.
  have: _pmeas0 = _pmeas1.
  apply nubbed_sortedP; elim (andP i); elim (andP i0); rewrite //=.
  intros.

  move: i i0.
  rewrite x; intros.
  have: i = i0.
  apply bool_irrelevance.
  move => ->.
  done.
Qed.

Section MeasOps.
  Context {A : choiceType}.
  Definition measMass (d : Meas A) :=
    integ d (fun _ => 1).
  Definition isDist (d : Meas A) :=
    measMass d == 1.
  Definition isSubdist (d : Meas A) :=
    measMass d <= 1.
  Definition measSupport (d : Meas A) := map snd (_pmeas d).
End MeasOps.

Section MeasMonad.
  Context {A B : choiceType}.
  Definition measRet (a : A) : Meas A := mkMeas ((1%PR,a) :: nil).
  Lemma isDist_ret : forall a, isDist (measRet a).
    intros; rewrite /isDist /measRet /measMass .
    rewrite integ_mkMeas //= integ_cons integ_nil //=.
  Qed.

  Definition measScale (r : posrat) (d : Meas B) : Meas B :=
    mkMeas (map (fun p => (r * p.1, p.2))%PR (_pmeas d)).

  Definition measSum (ds : list (Meas B)) : Meas B :=
    mkMeas (flatten (map (@_pmeas B) ds)).

  Definition measJoin (d : Meas ([choiceType of Meas B])) : Meas B :=
    measSum (map (fun p => measScale p.1 p.2) (_pmeas d)).

  Definition measMap {C : choiceType} (d : Meas A) (f : A -> C) : Meas C :=
    mkMeas (map (fun p => (p.1, f p.2)) (_pmeas d)).

  Definition measBind (d : Meas A) (f : A -> Meas B) : Meas B :=
    mkMeas (measJoin (measMap d (fun a => (f a)) )).
End MeasMonad.

Lemma integ_app {A : choiceType} (d1 d2 : PMeas A) f : integ (d1 ++ d2) f = integ d1 f + integ d2 f.
  unfold integ.
  rewrite big_cat //=.
Qed.

Lemma integ_measScale {A : choiceType} (d1 : Meas A) r f :
  integ (measScale r d1) f = r * (integ d1 f).
  unfold measScale; rewrite //=.
  rewrite integ_mkMeas /integ.
  rewrite big_map //=.
  rewrite big_distrr //=.
  apply eq_big.
  intros; done.
  intros.
  rewrite pmulrA.
  done.
Qed.

Lemma integ_measJoin {A : choiceType} (d : Meas ([choiceType of Meas A])) (f : A -> posrat) :
  integ (measJoin d) f = integ d (fun d' => integ d' f).
  rewrite /measJoin /measSum integ_mkMeas.
  destruct d as [d h]; rewrite //=.
  clear h.
  induction d.
  rewrite /measJoin /integ //= !big_nil.
  done.
  rewrite //=.
  rewrite integ_app.
  rewrite integ_mkMeas integ_cons IHd.
  congr (_ + _).
  rewrite /integ !big_map //=.
  rewrite big_distrr //=.
  apply eq_big.
  done.
  intros; rewrite pmulrA //=.
Qed.

Lemma integ_measBind {A B : choiceType} (d : Meas A) (df : A -> Meas B) f :
  integ (measBind d df) f = integ d (fun x => integ (df x) f).
  unfold measBind.
  rewrite integ_mkMeas.
  rewrite integ_measJoin.
  destruct d as [d h]; rewrite //=; clear h.
  rewrite integ_mkMeas.
  induction d.
  rewrite /integ big_map big_nil //=.
  rewrite integ_cons //= -IHd //= integ_cons //=.
Qed.

Notation "'ret' x" := (@measRet  _ x) (at level 75).
Notation "x <- c1 ; c2" := (@measBind _ _ c1 (fun x => c2))
   (right associativity, at level 81, c1 at next level).                       

Lemma integ_eq_fun {A : choiceType} (M : Meas A) (f1 f2 : A -> posrat) :
  (forall x, f1 x = f2 x) -> integ M f1 = integ M f2.
  intros.
  destruct M as [d h]; rewrite //=; clear h.
  induction d.
  rewrite !integ_nil //=.
  rewrite !integ_cons IHd.
  congr (_ + _).
  congr (_ * _).
  rewrite H; done.
Qed.

Lemma integ_ple_fun {A : choiceType} (M : Meas A) (f1 f2 : A -> posrat) :
  (forall x, f1 x <= f2 x) -> integ M f1 <= integ M f2.
  rewrite /integ => H; apply ple_sum => x.
  apply ple_mul_l; done.
Qed.

Lemma bindAssoc {A B C : choiceType} : forall (c1 : Meas A) (c2 : A -> Meas B) (c3 : B -> Meas C),
  (x <- (y <- c1; c2 y); c3 x) = (y <- c1; x <- c2 y; c3 x).
  intros; apply/MeasP => f.
  rewrite !integ_measBind.
  apply integ_eq_fun => x.
  rewrite integ_measBind.
  apply integ_eq_fun => y.
  done.
Qed.

Lemma bindRet_r {A : choiceType} (c : Meas A) :
  (x <- c; ret x) = c.
  apply/MeasP => f.
  rewrite integ_measBind.
  apply integ_eq_fun => x.
  rewrite integ_mkMeas //= integ_cons integ_nil .
  rewrite pmul1r paddr0 //=.
Qed.



Lemma measSupportP {A : choiceType} (c : Meas A) x :
  (x \in measSupport c) = (integ c (indicator x) != 0).
  apply Bool.eq_true_iff_eq; split => H.
  rewrite /measSupport in H.
  elim (mapP H) => h1 h2 h3.
  Check integ_nubbed_indicator_in.
  rewrite h3.
  rewrite (integ_nubbed_indicator_in c h1).
  destruct c; rewrite //=.
  elim (andP i) => _ /andP; elim => c1 c2.
  apply/contraT; rewrite negbK => hc.
  move/mapP: c1; elim; exists h1; rewrite //=.
  rewrite (eqP hc); done.
  destruct c as [c h]; rewrite //=; elim (andP h); done.
  done.
  apply/mapP; exists (integ c (indicator x), x).
  apply integ_nubbed_indicator_in_l; rewrite //=.
  destruct c as [c h]; rewrite //=; elim (andP h); done.
  done.
Qed.

Lemma measBind_swap {A B C : choiceType} (D1 : Meas A) (D2 : Meas B) (D3 : A -> B -> Meas C) :
  (x <- D1; y <- D2; D3 x y) = (y <- D2; x <- D1; D3 x y).
  apply/MeasP => f.
  rewrite !integ_measBind.
  erewrite integ_eq_fun; last first.
  move => x; rewrite integ_measBind; done.
  symmetry; 
  erewrite integ_eq_fun; last first.
  move => x; rewrite integ_measBind; done.
  rewrite /integ.

  have:
    \big[padd/0]_(p <- (_pmeas D2))
     (p.1 * \big[padd/0]_(p0 <- (_pmeas D1)) (p0.1 * \big[padd/0]_(p1 <- _pmeas (D3 p0.2 p.2)) (p1.1 * f p1.2))) =
    \big[padd/0]_(p <- _pmeas D2)
     (\big[padd/0]_(p0 <- _pmeas D1) (p.1 * p0.1 * \big[padd/0]_(p1 <- _pmeas (D3 p0.2 p.2)) (p1.1 * f p1.2))).
  apply eq_bigr => i _.
  rewrite big_distrr //=.
  apply eq_bigr => j _.
  rewrite pmulrA //=.
  move => ->.

  rewrite exchange_big; apply eq_bigr => i _.
  rewrite big_distrr; apply eq_bigr => j _ //=.

  rewrite (pmulrC j.1 i.1).
  rewrite pmulrA //=.
Qed.

Lemma mkMeas_nil {A : choiceType} : _pmeas (mkMeas (nil : PMeas A)) = nil.
  rewrite //= sort_keys_nil //=.
Qed.

Lemma measSupport_nil {A : choiceType} : measSupport (mkMeas (nil : PMeas A)) = nil.
  rewrite /measSupport mkMeas_nil //=.
Qed.

  Lemma psum_neq0 {A : eqType} (xs : seq A) f :
    \big[padd/0]_(x <- xs) f x != 0 ->
    exists x, (x \in xs) /\ f x != 0.
    induction xs.
    rewrite big_nil //=.
    rewrite big_cons.
    rewrite -padd0 negb_and; move/orP; elim => H.
    exists a; split.
    rewrite in_cons //= eq_refl //=.
    done.
    destruct (IHxs H).
    exists x; split.
    destruct H0.
    rewrite in_cons H0  orbT //=.
    destruct H0; done.
  Qed.

Lemma measSupport_bind {A B : choiceType} (c : Meas A) (d : A -> Meas B) x :
  x \in measSupport (a <- c; d a) -> exists y, y \in measSupport c /\ x \in measSupport (d y).
  rewrite measSupportP integ_measBind.
  rewrite /integ.
  move => H; apply psum_neq0 in H.
  elim H => y Hy.
  move: Hy => [hy1 hy2].
  exists y.2; split.
  apply/mapP; exists y; done.
  rewrite measSupportP.
  rewrite /integ.
  rewrite -pmul0 negb_or in hy2; move/andP: hy2; elim; done.
Qed.

Definition odflt_dep {A B} (p : A -> bool) (f : forall x (H : p x), B) (d : B) (x : A) : B :=
  match (Sumbool.sumbool_of_bool (p x)) with
  | left Heq => f x Heq
  | _ => d
           end.

Lemma odflt_depP {A B} (p : A -> bool) x (f : forall x (H : p x), B) d (H : p x) :
  odflt_dep p f d x = f x H.
rewrite /odflt_dep.
case: (Sumbool.sumbool_of_bool (p x)).
move=> a; have: H = a by apply bool_irrelevance.
move => ->; done.
rewrite H; done.
Qed.

Definition measBind_dep {A B : choiceType} (c : Meas A) (f : forall x, x \in measSupport c -> Meas B) : Meas B :=
  (x <- c; odflt_dep (fun x => x \in measSupport c) f (mkMeas nil) x).

Definition measSupport_bind_dep {A B : choiceType} (c : Meas A) (f : forall x, x \in measSupport c -> Meas B) x :
  x \in measSupport (measBind_dep c f) -> exists y (H : y \in measSupport c), x \in measSupport (f y H).
  rewrite /measBind_dep.
  intros.
  apply measSupport_bind in H.
  elim H => y; elim; intros.
  exists y,  H0.
  rewrite odflt_depP in H1.
  done.
Qed.

Lemma integ_eq_fun_dep {A : choiceType} (M : Meas A) (f1 f2 : A -> posrat) :
  (forall x, x \in measSupport M -> f1 x = f2 x) -> integ M f1 = integ M f2.
  intros.
  
  rewrite /integ.

  rewrite big_seq_cond.
  rewrite (big_seq_cond _ (fun p => p.1 * f2 p.2)).
  apply eq_big; rewrite //=.
  intros.
  move/andP: H0 => [H0 _].

  rewrite H.
  done.
  apply/mapP; exists i; done.
Qed.


Lemma isSubdist_bind {A B : choiceType} (c : Meas A) (f : A -> Meas B) :
  isSubdist c -> (forall x, isSubdist (f x)) -> isSubdist (x <- c; f x).
  rewrite /isSubdist /measMass integ_measBind //= => h1 h2.
  eapply ple_trans.
  apply integ_ple_fun.
  instantiate (1 := fun _ => 1); rewrite //=.
  done.
Qed.

Lemma isSubdist_ret {A : choiceType} (c : A) : isSubdist (ret c).
  rewrite /isSubdist.
  rewrite (eqP (isDist_ret c)) //=.
Qed.

Check integ.

Lemma integ_measMap {A B : choiceType} (m : Meas A) (f : A -> B) g :
  integ (measMap m f) g = integ m (fun x => g (f x)).
  rewrite /measMap integ_mkMeas /integ big_map; apply eq_big; rewrite //=.
Qed.

Lemma integ_ret {A : choiceType} (x : A) g :
  integ (ret x) g = g x.
  rewrite /measRet integ_mkMeas integ_cons integ_nil paddr0.
  have -> : (1, x).1 = 1 by rewrite //=.
  have -> : (1, x).2 = x by rewrite //=.
  rewrite pmul1r //=.
Qed.

Lemma measMap_ret {A B : choiceType} (x : A) (f : A -> B) :
  measMap (ret x) f = ret (f x).
  apply/MeasP => g; rewrite integ_measMap !integ_ret //=.
Qed.

Lemma measMap_bind {A B C : choiceType} (m : Meas A) (c : A -> Meas B) (f : B -> C) :
  (measMap (x <- m; c x) f) = (x <- m; measMap (c x) f).
  apply/MeasP => g.
  rewrite !integ_measMap !integ_measBind.
  apply integ_eq_fun => x.
  rewrite integ_measMap //=.
Qed.

Lemma measMap_measMap {A B C : choiceType} (m : Meas A) (f : A -> B) (g : B -> C) :
  measMap (measMap m f) g = measMap m (fun x => g (f x)).
  apply/MeasP => h.
  rewrite !integ_measMap //=.
Qed.

Lemma measBind_measMap {A B C : choiceType} (m : Meas A) (f : A -> B) (c : B -> Meas C) :
  (x <- measMap m f; c x) = (x <- m; c (f x)).
  apply/MeasP => g; rewrite !integ_measBind !integ_measMap //=.
Qed.

Lemma measBind_eqP {A B : choiceType} (m : Meas A) (c1 c2 : A -> Meas B) :
  (forall x, x \in measSupport m -> c1 x = c2 x) -> ((x <- m; c1 x) = (x <- m; c2 x)).
  move=> H; apply/MeasP => f.
  rewrite !integ_measBind; apply integ_eq_fun_dep => x Hx.
  rewrite (H x Hx) //=.
Qed.

Lemma bindRet_l {A B : choiceType} (a : A) (c : A -> Meas B) :
  (x <- (ret a); c x) = c a.
  apply/MeasP => f; rewrite integ_measBind integ_ret //=.
Qed.

Lemma big_padd_foldr (xs : seq posrat) :
  foldr padd 0 xs = \big[padd/0]_(x <- xs) x.
  induction xs; rewrite ?big_nil ?big_cons //=.
  rewrite IHxs //=.
Qed.

Lemma isSubdist_mkMeas {A : choiceType} (pm : PMeas A) :
  (foldr padd 0 (map fst pm ) <= 1) -> isSubdist (mkMeas pm).
  rewrite /isSubdist /measMass integ_mkMeas => H.
  have -> : integ pm (fun _ => 1) = foldr padd 0 (map fst pm).
  rewrite big_padd_foldr /integ big_map; apply eq_bigr => x _; rewrite pmulr1 //=.
  done.
Qed.

Ltac isSubdist_tac :=
  match goal with
    | [ |- is_true (isSubdist (ret _))] => apply isSubdist_ret

    | [ |- is_true (isSubdist (measBind _ _ )) ] =>
        apply isSubdist_bind; [ isSubdist_tac | move => x; isSubdist_tac ]

    | [ |- is_true (isSubdist (mkMeas _))] =>
        apply isSubdist_mkMeas; rewrite //=
                                       end.
