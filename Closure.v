
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap tuple.
Require Import Posrat Premeas Meas Program Aux.


Definition isClosure {A B : choiceType} (R : {meas A} -> {meas B} -> bool) (mu : {meas A}) (eta : {meas B}) (w : {meas {meas A} * {meas B}}) :=
  [&& (mu == (p <- w; p.1)), (eta == (p <- w; p.2)) & (all (fun p => [&& isdist p.1, isdist p.2 & R p.1 p.2])) (support w)].


Definition closure {A B : choiceType} R (mu : {meas A}) (eta : {meas B}) := exists w, isClosure R mu eta w.

Lemma closure_bind {A B C : choiceType} R (c : {meas A}) (f : A -> {meas B}) (g : A -> {meas C}) :
  (forall x, x \in support c -> closure R (f x) (g x)) ->
  closure R (x <- c; f x) (x <- c; g x).
  move => H.
  exists (mbind_dep c (fun x p => xchoose (H x p))).
  apply/and3P; split.

  rewrite /mbind_dep mbindA.
  apply/eqP/measP => h; rewrite !integ_mbind.
  apply integ_eq_fun => x Hx.
  rewrite odflt_depP.

  have H2 := xchooseP (H x Hx); move/and3P: H2; elim => h1 h2 h3.
  rewrite -(eqP h1); done.

  rewrite /mbind_dep mbindA.
  apply/eqP/measP => h; rewrite !integ_mbind.
  apply integ_eq_fun => x Hx.
  rewrite odflt_depP.
  have H2 := xchooseP (H x Hx); move/and3P: H2; elim => h1 h2 h3.
  rewrite -(eqP h2); done.

  apply/allP => x.
  move/support_bind_dep; elim => y; elim => h hin.

  have H2 := xchooseP (H y h); move/and3P: H2; elim => h1 h2 h3.
  move/allP: h3 => h3.
  apply h3.
  done.
Qed.

Lemma closure_seq {A B C D : choiceType} (m : {meas A}) (m' : {meas B}) (f : A -> {meas C}) (f' : B -> {meas D}) R1 R2 :
  closure R1 m m' -> (forall a b, isdist a -> isdist b -> R1 a b -> closure R2 (mbind a f) (mbind b f')) -> closure R2 (mbind m f) (mbind m' f').
  move => H H2.
  destruct H as [d Hd]; move/and3P: Hd; elim => h1 h2 h3.
  move/eqP: h1 => h1; move/eqP: h2 => h2.
  subst; rewrite !measE.
  apply closure_bind => x Hx.
  apply H2; move/and3P: (allP h3 _ Hx); elim; intros; done.
Qed.

Lemma id_closure {A B : choiceType} (R : {meas A} -> {meas B} -> bool) (mu : {meas _}) (eta : {meas _}):
  isdist mu -> isdist eta -> R mu eta -> closure R mu eta.
  intros; exists (ret (mu, eta)).
  apply/and3P; split.
  rewrite ret_bind //=.
  rewrite ret_bind //=.
  rewrite support_ret all_seq1 //=.
  apply/and3P; split ;done.
Qed.
  
Lemma closure_implies {A B : choiceType} (R : {meas A} -> {meas B} -> bool) (R' : _ -> _ -> bool) :
  (forall mu eta, R mu eta -> R' mu eta) -> forall mu eta, closure R mu eta -> closure R' mu eta.
  move => H mu eta; case => l Hl; move/and3P: Hl => [h1 h2 h3].
  rewrite (eqP h1) (eqP h2); apply closure_bind => x Hx.
  apply id_closure; move/and3P: (allP h3 _ Hx); elim.
  move/and3P: (allP h3 _ Hx); elim; rewrite //=.
  move/and3P: (allP h3 _ Hx); elim; rewrite //=.
  intros; apply H; done.
Qed.


Lemma closure_fmap {A B C D : choiceType} (f1 : A -> C) (f2 : B -> D) (R : {meas C} -> {meas D} -> bool) (mu : {meas A}) (eta : {meas B})
  : closure (fun mua mub => R (mua <$> f1) (mub <$> f2)) mu eta ->
    closure R (mu <$> f1) (eta <$> f2).
  elim => [l Hl]; move/and3P: Hl => [h1 h2 h3].
  exists (p <- l; ret (p.1 <$> f1, p.2 <$> f2)).
  apply/and3P; split.

  rewrite (eqP h1) !mbindA.
  apply/eqP; apply mbind_eqP => x Hx.
  rewrite ret_bind //= measMapE //=.

  rewrite (eqP h2) !mbindA.
  apply/eqP; apply mbind_eqP => x Hx.
  rewrite ret_bind //= measMapE //=.

  apply/allP => x.
  move/support_bindP; elim => y; elim => hy1 hy2.
  rewrite support_ret in_cons orbF in hy2; rewrite (eqP hy2) //=.
  move/allP: h3; move/(_ _ hy1).
  rewrite !isdist_fmap //=.
Qed.

Lemma eq_closure {A : choiceType} (mu eta : {meas A}) :
  closure (fun x y => x == y) mu eta -> mu = eta.
  elim => c Hc; simpl in *.
  elim (and3P Hc); simpl => h1 h2 h3.
  rewrite (eqP h1) (eqP h2); apply mbind_eqP => x Hx.
  move/allP: h3.
  move/(_ _ Hx)/and3P; elim => _ _ /eqP ->; done.
Qed.

(*
Definition coupling {A B : choiceType} (R : A -> B -> bool) (mu : {meas A}) (eta : {meas B}) :=
  exists d, [&& mu == d <$> fst, eta == d <$> snd & all (fun p => R p.1 p.2) (support d)].

Section couplingsec.
  Context {A B : choiceType} (R : A -> B -> bool) (mu : {meas A}) (eta : {meas B}).
  Check closure.

  Lemma trythis : closure (fun a b => all (fun x => all (fun y => R x y) (support b)) (support a)) mu eta -> coupling R mu eta.
    elim => d.
    move/and3P; elim.
    move/eqP => -> /eqP => ->. 
    move/allP => H.
    rewrite /coupling.
    exists (p <- d; x <- fst p; y <- snd p; ret (x,y)).
    apply/and3P; split.
    rewrite !measE.
    apply/eqP.
    apply mbind_eqP => p Hp; rewrite !measE.
    munder (rewrite !measE; munder (rewrite !measE)).
    munder (rewrite mbind_irrel).

    admit.
    admit.
    apply/allP => x.
    move/support_bindP; elim => p; elim => Hp; move/support_bindP; elim => a; elim => Ha; move/support_bindP; elim => b; elim => Hb.
    rewrite support_ret mem_seq1; move/eqP => -> //=.
    move: (H p Hp).
    move/allP/(_ _ Ha)/allP/(_ _ Hb); done.
    rewrite 
    Check mbind_irrel.
    mun
    rewrite -(bind_ret p.1).
    rewrite mbindA; apply mbind_eqP => x.
    app
    app
    exists 
    move/all2P.
    rewrite /isClosure.
*)