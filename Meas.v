
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
Require Import PIOA.Posrat PIOA.Premeas Aux.

(*****************************************************************************)
(* {meas A} = linear combinations of posrat over A, where A is choicetype    *)


(* Section about integ *)
(* Section about mass *)
(* Section about support *)



Section MeasDef.
  Variables (A : choiceType).
  Structure Meas : Type :=
    {
      _pmeas :> PMeas A;
      _ : canonical_keys _pmeas && nubbed _pmeas
    }.
  Definition meas_of (_ : phant A) := Meas.
End MeasDef.

Arguments _pmeas [A].
Identity Coercion type_of_meas : meas_of >-> Meas.
Notation "{meas T }" := (@meas_of _ (Phant T)) (format "{meas  T }") : type_scope.

Section MeasCanonicals.
  Variables (A : choiceType).

Canonical meassub  := Eval hnf in [subType for (@_pmeas A)].
Definition measEqmix  := Eval hnf in [eqMixin of {meas A} by <:].
Canonical measEqtype := Eval hnf in EqType {meas A} (measEqmix).
Definition measChoicemix  := Eval hnf in [choiceMixin of {meas A} by <: ].
Canonical measChoicetype := Eval hnf in ChoiceType {meas A} (measChoicemix).
End MeasCanonicals.

Definition mkMeas {A : choiceType} (d : PMeas A) : {meas A}.
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

Lemma in_pmeas_neq0 {A : choiceType} (m : {meas A}) x :
  x \in _pmeas m -> x.1 != 0.
  destruct m; simpl.
  move/andP: i; elim => [_ h].
  move/andP: h; elim => h1 h2.
  rewrite /measReduced in h1.
  intros.
  apply/contraT; rewrite negbK => hc.
  move/mapP: h1.
  elim.
  exists x.
  done.
  rewrite (eqP hc); done.
Qed.


Section MeasOps.
  Context {A : choiceType}.
  Definition mass (d : {meas A}) :=
    integ d (fun _ => 1).
  Definition dist (d : {meas A}) :=
    mass d == 1.
  Definition subdist (d : {meas A}) :=
    mass d <= 1.
  Definition support (d : {meas A}) := map snd (_pmeas d).
End MeasOps.

Section MeasMonad.
  Context {A B : choiceType}.

  Definition mret (a : A) : {meas A} := mkMeas ((1%PR,a) :: nil).


  Definition mscale (r : posrat) (d : {meas B}) : {meas B} :=
    mkMeas (map (fun p => (r * p.1, p.2))%PR (_pmeas d)).

  Definition msum (ds : list ({meas B})) : {meas B} :=
    mkMeas (flatten (map (@_pmeas B) ds)).

  Definition mjoin (d : {meas {meas B}}) : {meas B} :=
    msum (map (fun p => mscale p.1 p.2) (_pmeas d)).

  Definition mmap {C : choiceType} (d : {meas A}) (f : A -> C) : {meas C} :=
    mkMeas (map (fun p => (p.1, f p.2)) (_pmeas d)).

  Definition mbind (d : {meas A}) (f : A -> {meas B}) : {meas B} :=
    mkMeas (mjoin (mmap d (fun a => (f a)) )).
End MeasMonad.

Lemma mkMeas_nil {A : choiceType} : _pmeas (mkMeas (nil : PMeas A)) = nil.
  rewrite //= sort_keys_nil //=.
Qed.


Notation "'ret' x" := (@mret  _ x) (at level 75).
Notation "x <- c1 ; c2" := (@mbind _ _ c1 (fun x => c2))
   (right associativity, at level 81, c1 at next level).                       
Notation "m <$> f" := (x <- m; ret (f x)) (at level 50). (* mmap is only used internally *)

Notation "a ** b" := (x <- a; y <- b; ret (x,y)) (at level 30).

Definition mbind_dep {A B : choiceType} (c : {meas A}) (f : forall x, x \in support c -> {meas B}) : {meas B} :=
  (x <- c; odflt_dep (fun x => x \in support c) f (mkMeas nil) x).

(* For each section: 
   need:
    1.  how it interacts with: 
        * ret
        * bind
        * fmap
        * prod
        * scale

    2. any other useful properties
*)

(* Properties about integ, along with basic equivalences between return and bind *)

Lemma integ_ple_fun {A : choiceType} (M : {meas A}) (f1 f2 : A -> posrat) :
  (forall x, x \in support M -> f1 x <= f2 x) -> integ M f1 <= integ M f2.
  rewrite /integ.
  rewrite big_seq_cond.
  rewrite (big_seq_cond _ (fun p => p.1 * f2 p.2)).
  move => H.
  apply ple_sum => x.
  rewrite andbT => Hx.
  apply ple_mul_l.
  apply H.
  apply/mapP; exists x; done.
Qed.

Lemma integ_eq_fun {A : choiceType} (M : {meas A}) (f1 f2 : A -> posrat) :
  (forall x, x \in support M -> f1 x = f2 x) -> integ M f1 = integ M f2.
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


Definition measP {A : choiceType} (d1 d2 : {meas A}) :
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

Lemma integ_ret {A : choiceType} (x : A) g :
  integ (ret x) g = g x.
  rewrite /mret integ_mkMeas integ_cons integ_nil paddr0.
  have -> : (1, x).1 = 1 by rewrite //=.
  have -> : (1, x).2 = x by rewrite //=.
  rewrite pmul1r //=.
Qed.

Lemma integ_mscale {A : choiceType} (d1 : {meas A}) r f :
  integ (mscale r d1) f = r * (integ d1 f).
  unfold mscale; rewrite //=.
  rewrite integ_mkMeas /integ.
  rewrite big_map //=.
  rewrite big_distrr //=.
  apply eq_big.
  intros; done.
  intros.
  rewrite pmulrA.
  done.
Qed.

Lemma integ_mjoin {A : choiceType} (d : {meas {meas A}}) (f : A -> posrat) :
  integ (mjoin d) f = integ d (fun d' => integ d' f).
  rewrite /mjoin /msum integ_mkMeas.
  destruct d as [d h]; rewrite //=.
  clear h.
  induction d.
  rewrite /mjoin /integ //= !big_nil.
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

Lemma integ_mbind {A B : choiceType} (d : {meas A}) (df : A -> {meas B}) f :
  integ (mbind d df) f = integ d (fun x => integ (df x) f).
  unfold mbind.
  rewrite integ_mkMeas.
  rewrite integ_mjoin.
  destruct d as [d h]; rewrite //=; clear h.
  rewrite integ_mkMeas.
  induction d.
  rewrite /integ big_map big_nil //=.
  rewrite integ_cons //= -IHd //= integ_cons //=.
Qed.

(* HERE: basic monadic stuff *)

Lemma mbindA {A B C : choiceType} : forall (c1 : {meas A}) (c2 : A -> {meas B}) (c3 : B -> {meas C}),
  (x <- (y <- c1; c2 y); c3 x) = (y <- c1; x <- c2 y; c3 x).
  intros; apply/measP => f.
  rewrite !integ_mbind.
  apply integ_eq_fun => x Hx.
  rewrite integ_mbind.
  apply integ_eq_fun => y Hy.
  done.
Qed.

Lemma bind_ret {A : choiceType} (c : {meas A}) :
  (x <- c; ret x) = c.
  apply/measP => f.
  rewrite integ_mbind.
  apply integ_eq_fun => x Hx.
  rewrite integ_mkMeas //= integ_cons integ_nil .
  rewrite pmul1r paddr0 //=.
Qed.

Lemma ret_bind {A B : choiceType} (a : A) (c : A -> {meas B}) :
  (x <- (ret a); c x) = c a.
  apply/measP => f; rewrite integ_mbind integ_ret //=.
Qed.

Lemma mbind_swap {A B C : choiceType} (D1 : {meas A}) (D2 : {meas B}) (D3 : A -> B -> {meas C}) :
  (x <- D1; y <- D2; D3 x y) = (y <- D2; x <- D1; D3 x y).
  apply/measP => f.
  rewrite !integ_mbind.
  erewrite integ_eq_fun; last first.
  move => x; rewrite integ_mbind; done.
  symmetry; 
  erewrite integ_eq_fun; last first.
  move => x; rewrite integ_mbind; done.
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

Lemma integ_mfmap {A B : choiceType} (m : {meas A}) (f : A -> B) g :
  integ (m <$> f) g = integ m (fun x => g (f x)).
  rewrite integ_mbind; apply integ_eq_fun => x Hx; rewrite integ_ret //=.
Qed.

Lemma integ_mprod {A B : choiceType} (m1 : {meas A}) (m2 : {meas B}) f :
  integ (m1 ** m2) f =
  integ m1 (fun x => integ m2 (fun y => f (x,y))).
  rewrite !integ_mbind.
  apply integ_eq_fun => x Hx.
  rewrite integ_mbind; apply integ_eq_fun => y Hy.
  rewrite integ_ret //=.
Qed.

Lemma integ_mprod_sym {A B : choiceType} (m1 : {meas A}) (m2 : {meas B}) f :
  integ (m1 ** m2) f =
  integ (m2 ** m1) (fun p => f (p.2, p.1)).
  rewrite mbind_swap.
  rewrite !integ_mbind.
  apply integ_eq_fun => x Hx.
  rewrite !integ_mbind.
  apply integ_eq_fun => y Hy.
  rewrite !integ_ret //=.
Qed.


Lemma integ_neq0 {A : choiceType} (m : {meas A}) f :
  (integ m f != 0) = (has (fun x => f x != 0) (support m)).
  rewrite /integ.
  rewrite psum_neq0.
  rewrite has_map.
  apply eq_in_has => x Hx.
  rewrite //=.
  rewrite -pmul0 negb_or.
  have: x.1 != 0.
  eapply in_pmeas_neq0.
  apply Hx.
  move => ->; rewrite //=.
Qed.

Lemma integ_const_fun_val {A B : choiceType} (m1 : {meas A}) (m2 : {meas B}) (f : A -> posrat) (g : B -> posrat) :
  mass m1 = mass m2 ->
  (exists a, (forall x, x \in support m1 -> f x = a) /\ (forall y, y \in support m2 -> g y = a)) ->
  integ m1 f = integ m2 g.
  
  move => h1 h2.
  elim h2 => a; elim => h3 h4.

  have: integ m1 f = a * mass m1.
  rewrite /mass /integ big_distrr //=.
  rewrite big_seq_cond.
  rewrite (big_seq_cond _ (fun i => a * (i.1 * 1))).
  apply eq_big; rewrite //=.
  move => i; move/andP => [Hi _].
  rewrite h3.
  rewrite pmulr1 pmulrC //=.
  apply/mapP; exists i; done.
  move => ->.

  have: integ m2 g = a * mass m2.
  rewrite /mass /integ big_distrr //=.
  rewrite big_seq_cond.
  rewrite (big_seq_cond _ (fun i => a * (i.1 * 1))).
  apply eq_big; rewrite //=.
  move => i; move/andP => [Hi _].
  rewrite h4.
  rewrite pmulr1 pmulrC //=.
  apply/mapP; exists i; done.
  move => ->.

  rewrite h1 //=.
Qed.

Lemma integ_const {A : choiceType} (m : {meas A}) (c : posrat) :
  integ m (fun _ => c) = mass m * c.
  rewrite /integ; destruct m.
  rewrite -big_distrl //=.
  rewrite /mass /integ //=.
  congr (_ * _).
  apply eq_big.
  done.
  move => i0 _; rewrite pmulr1 //=.
Qed.

(* end integ *)

(* equality lemmas *)

Lemma mbind_eqP {A B : choiceType} (m : {meas A}) (c1 c2 : A -> {meas B}) :
  (forall x, x \in support m -> c1 x = c2 x) -> ((x <- m; c1 x) = (x <- m; c2 x)).
  move=> H; apply/measP => f.
  rewrite !integ_mbind; apply integ_eq_fun => x Hx.
  rewrite (H x Hx) //=.
Qed.
 
Lemma prod_dirac_Pr {A B : choiceType} (m : {meas A * B}) a u :
  (forall x, x \in support m -> x.2 = a) ->
  (u = m <$> fst) ->
  m = u ** (ret a).
  intros; subst; apply/measP => f.
  rewrite integ_mprod.
  rewrite integ_mbind.
  apply integ_eq_fun => x Hx.
  rewrite !integ_ret.
 
  rewrite -(H _ Hx); destruct x; done.
Qed.


Lemma mbind_irrel {A B : choiceType} (m1 : {meas A}) (f : {meas B}) :
  (x <- m1; f) = mscale (mass m1) f.
  apply measP => g; rewrite integ_mbind.
  rewrite integ_const.
  rewrite integ_mscale //=.
Qed.

(* begin support and mass *)

Lemma uniq_support {A : choiceType} (c : {meas A}) :
  uniq (support c).
  destruct c; elim (andP i) => i1 i2.
  move/andP: i2; elim => i2 i3.
  done.
Qed.

Lemma supportP {A : choiceType} (c : {meas A}) x :
  (x \in support c) = (integ c (indicator x) != 0).
  apply Bool.eq_true_iff_eq; split => H.
  rewrite /support in H.
  elim (mapP H) => h1 h2 h3.
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

Lemma support_nil {A : choiceType} : support (mkMeas (nil : PMeas A)) = nil.
  rewrite /support mkMeas_nil //=.
Qed.

Lemma support_ret {A : choiceType} (x : A) :
  support (ret x) = [:: x].
  have: perm_eq (support (ret x)) [:: x].
  apply uniq_perm_eq.
  destruct (ret x).
  elim (andP i) => i1 i2.
  move/andP: i2; elim => i2 i3.
  apply i3.
  done.
  move => y; rewrite supportP integ_ret /Premeas.indicator in_cons in_nil orbF; case (y ==x); done.
  move => H; by apply perm_eq_small.
Qed.


Lemma support_bindE {A B : choiceType} (c : {meas A}) (d : A -> {meas B}) :
  support (x <- c; d x) =i flatten [seq (support (d x)) | x <- support c].
  move => x.
  rewrite supportP !integ_mbind integ_neq0.
  apply Bool.eq_true_iff_eq; split.
  move/hasP; elim => a Ha Ha2.
  rewrite integ_neq0 in Ha2.
  move/hasP: Ha2; elim => b Hb.
  rewrite indicator_neq0; move/eqP => ->.
  apply/flattenP; exists (support (d a)).
  apply/mapP; exists a; done.
  done.
  move/flattenP; elim => b.
  move/mapP; elim => a Ha -> Hx.
  apply/hasP; exists a; rewrite //=.
  rewrite integ_neq0; apply/hasP; exists x; rewrite ?indicator_neq0 //=.
Qed.

Lemma support_bindP {A B : choiceType} (c : {meas A}) (d : A -> {meas B}) x :
  reflect (exists a, a \in support c /\ x \in support (d a)) (x \in support (x <- c; d x)).
  apply/(iffP idP); rewrite support_bindE.
  move/flattenP; elim => b; move/mapP; elim => a Ha -> Hb.
  exists a; done.

  elim => a; elim => h1 h2; apply/flattenP; exists (support (d a)); rewrite //=.
  apply/mapP; exists a; done.
Qed.

Lemma support_bind_dep {A B : choiceType} (c : {meas A}) (f : forall x, x \in support c -> {meas B}) x :
  x \in support (mbind_dep c f) -> exists y (H : y \in support c), x \in support (f y H).
  rewrite /mbind_dep.
  intros.
  move/support_bindP: H; elim => y; elim; intros.
  exists y, H.
  rewrite odflt_depP in H0.
  done.
Qed.

Lemma support_mprodE {A B : choiceType} (m1 : {meas A}) (m2 : {meas B}) :
  (support (m1 ** m2)) =i [seq (x,y) | x <- support m1, y <- support m2].
  move => x.
  apply Bool.eq_true_iff_eq; split.
  move/support_bindP; elim => a; elim => Ha.
  move/support_bindP; elim => b; elim => Hb.
  rewrite support_ret mem_seq1; move/eqP => ->.
  apply/allpairsP; exists (a,b); split; rewrite //=.

  move/allpairsP; elim => p; elim => H1 H2 ->.
  apply/support_bindP; exists p.1; split; rewrite //=.
  apply/support_bindP; exists p.2; split; rewrite //=.
  rewrite support_ret mem_seq1 //=.
Qed.

Lemma support_fmap {A B : choiceType} (m1 : {meas A}) (f : A -> B) :
  support (m1 <$> f) =i map f (support m1).
  move => x;
  apply Bool.eq_true_iff_eq; split.
  move/support_bindP; elim => a [H1 H2].
  apply/mapP; exists a; rewrite //=.
  rewrite support_ret mem_seq1 in H2; rewrite (eqP H2) //=.
  move/mapP; elim  => a [h1 h2].
  apply/support_bindP; exists a; split; rewrite //=.
  rewrite support_ret h2  in_cons eq_refl in_nil //=.
Qed.

Lemma support_mscale_neq0 {A B : choiceType} (m : {meas A}) (r : posrat) (Hr : r != 0) :
  support (mscale r m) =i support m.
  move => x; rewrite !supportP integ_mscale -pmul0 negb_or Hr andTb //=.
Qed.

Lemma support_mscale_eq0 {A B : choiceType} (m : {meas A}) :
  support (mscale 0 m) = nil.
  have: perm_eq (support (mscale 0 m)) nil.
  apply uniq_perm_eq.
  apply uniq_support.
  done.
  move => x; rewrite in_nil supportP integ_mscale pmul0r //=.
  move => H; apply perm_eq_small; done.
Qed.  

(* Subdist and dist *)  

Lemma mass_ret {A : choiceType} (c : A) : mass (ret c) = 1.
  rewrite /mass integ_ret //=.
Qed.

Lemma mass_bind_eq {A B : choiceType} (c : {meas A}) (d : A -> {meas B}) r :
  mass c = r -> (forall x, x \in support c -> mass (d x) = r) -> mass (x <- c; d x) = r * r.
  move => Hc Hd.
  rewrite /mass integ_mbind.
  have -> : r * r = integ c (fun _ => r).
  by rewrite integ_const Hc //=.
  apply integ_eq_fun => x Hx.
  rewrite /mass in Hd.
  rewrite (Hd x Hx) //=.
Qed.

Lemma mass_bind_le {A B : choiceType} (c : {meas A}) (d : A -> {meas B}) r :
  mass c <= r -> (forall x, x \in support c -> mass (d x) <= r) -> mass (x <- c; d x) <= r * r.
  move => Hc Hd.
  rewrite /mass integ_mbind.
  have Hi: integ c (fun _ => r) = (mass c) * r.
  by rewrite integ_const pmulrC //=.

  eapply ple_trans.
  instantiate (1 := integ c (fun _ => r)).
  apply integ_ple_fun => x Hx.
  rewrite /mass in Hd; apply Hd.
  done.
  rewrite integ_const.
  apply ple_mul_r.
  done.
Qed.

Lemma dist_subdist {A : choiceType} (c : {meas A}) : dist c -> subdist c.
  rewrite /dist /subdist; move/eqP => ->; done.
Qed.

Lemma dist_ret {A : choiceType} (c : {meas A}) : dist (ret c).
  rewrite /dist mass_ret //=.
Qed.

Lemma dist_bind {A B : choiceType} (c : {meas A}) (d : A -> {meas B}) :
  dist c -> (forall x, x \in support c -> dist (d x)) -> dist (x <- c; d x).
  move => h1 h2; rewrite /dist (mass_bind_eq _ _ 1).
  done.
  move/eqP:  h1; done.
  move => x Hx; move/eqP: (h2 x Hx); done.
Qed.

Lemma mass_nil {A : choiceType} : mass (mkMeas (nil : PMeas A)) = 0.
  rewrite /mass integ_mkMeas integ_nil //=.
Qed.

Lemma mass_eq0 {A : choiceType} (m : {meas A}) : (mass m == 0) = (m == mkMeas nil).
  apply Bool.eq_true_iff_eq; split.
  move/eqP.
  move => H; apply/eqP; apply measP => f.
  rewrite integ_mkMeas integ_nil //=.

  apply/eqP/contraT; rewrite /integ.
  rewrite psum_neq0; move/hasP; elim => x Hx.
  rewrite -pmul0; rewrite negb_or; move/andP => [h1 h2].

  have Hc1: x.2 \in support m.
  apply/mapP; exists x; done.

  have Hc2 : x.2 \notin support m.
  rewrite supportP negbK.
  rewrite /mass in H.
  have: integ m (indicator x.2) <= integ m (fun _ => 1).
  apply integ_ple_fun.
  move => y; rewrite /indicator; case (x.2 == y); done.
  move => Hle.
  rewrite -ple_le0.
  eapply ple_trans.
  apply Hle.
  rewrite H; done.
  rewrite Hc1 in Hc2; done.

  move/eqP => ->; rewrite /mass integ_mkMeas integ_nil //=.
Qed.  

Lemma mass_neq0 {A : choiceType} (m : {meas A}) :
  reflect (exists a, a \in support m) (mass m != 0).
  apply (iffP idP).

  rewrite /mass psum_neq0; move/hasP; elim => x Hx _; exists x.2.
  apply/mapP; exists x; done.

  elim => a Ha.
  rewrite /mass psum_neq0; apply/hasP.
  move/mapP: Ha; elim => x Hx Heq; subst.
  exists x.
  done.
  rewrite pmulr1.
  apply (in_pmeas_neq0 m); done.
Qed.

Lemma mass_bindE {A B : choiceType} (m1 : {meas A}) (c : A -> {meas B}) :
  mass (x <- m1; c x) = integ m1 (fun x => mass (c x)).
  rewrite /mass integ_mbind //=.
Qed.

Lemma mass_fmap {A B : choiceType} (m : {meas A}) (f : A -> B):
  mass (m <$> f) = mass m.
  rewrite mass_bindE /mass.
  apply integ_eq_fun => x Hx; rewrite integ_ret //=.
Qed.


Lemma in_support_ret {A : choiceType} (x : A) y :
  (y \in support (ret x)) = (y == x).
  rewrite support_ret in_cons in_nil orbF //=.
Qed.

(* adding measures together *)

Definition madd {A : choiceType} (m1 m2 : {meas A}) : {meas A} :=
  mkMeas ((_pmeas m1) ++ (_pmeas m2)).

Notation "m1 +m m2" := (madd m1 m2) (at level 30).

Lemma integ_madd {A : choiceType} (m1 m2 : {meas A}) f :
  integ (m1 +m m2) f = integ m1 f + integ m2 f.
  rewrite /madd integ_mkMeas integ_app //=.
Qed.

Lemma madd_bind {A B : choiceType} (m1 m2 : {meas A}) (c : A -> {meas B}) :
  (x <- (m1 +m m2); c x) = (x <- m1; c x) +m (x <- m2; c x).
  apply/measP => g.
  rewrite !integ_mbind !integ_madd !integ_mbind //=.
Qed.

Lemma integ_add_f {A : choiceType} (m : {meas A}) (f1 f2 : A -> posrat) :
  integ m (fun x => f1 x + f2 x) = integ m f1 + integ m f2.
  rewrite /integ.
  have -> : \big[padd/0]_(p <- _pmeas m) (p.1 * (f1 p.2 + f2 p.2))
         = \big[padd/0]_(p <- _pmeas m) ((p.1 * f1 p.2) + (p.1 * f2 p.2)).
  apply eq_big; rewrite //=.
  intros; rewrite pmulrDr //=.
  rewrite big_split //=.
Qed.

Lemma bind_madd {A B : choiceType} (m : {meas A}) (c1 c2 : A -> {meas B}) :
  (x <- m; (c1 x) +m (c2 x)) = (x <- m; c1 x) +m (x <- m; c2 x).
  apply/measP => g.
  rewrite !integ_mbind !integ_madd !integ_mbind. 
  have -> : 
  integ m (fun x : A => integ (c1 x +m c2 x) g) =
  integ m (fun x => integ (c1 x) g + integ (c2 x) g).
  apply integ_eq_fun => x Hx; rewrite integ_madd //=.
  rewrite integ_add_f //=.
Qed.

Lemma maddA {A : choiceType} (m1 m2 m3 : {meas A}) :
  madd m1 (madd m2 m3) = madd (madd m1 m2) m3.
  apply/measP => f; rewrite !integ_madd paddrA //=.
Qed.



(* to port

Ltac support_tac H :=
  match type of H with
  | is_true (_ \in support (mbind _ _)) =>
    let y := fresh "x" in
    let Hy1 := fresh "H" y in
    let Hy2 := fresh "H" y in
    elim (support_bind _ _ _ H) => y; elim => Hy1 Hy2; support_tac Hy1; support_tac Hy2; clear H
  | is_true (_ \in support (mret _)) =>
    let h := fresh "Heq" in
    rewrite in_support_ret in H; move: (eqP H) => h
  | _ => idtac
  end. 
*)



(* TO deal with *)







