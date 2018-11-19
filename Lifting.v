
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
Require Import Posrat Premeas Meas Program Aux.

Definition isLifting {A B : choiceType} (R : {meas A} -> {meas B} -> bool) (mu : {meas A}) (eta : {meas B}) (w : {meas {meas A} * {meas B}}) :=
  [&& (mu == (p <- w; p.1)), (eta == (p <- w; p.2)) & (all (fun p => R p.1 p.2 && (mass p.1 == mass p.2)) (support w))].

Definition lifting {A B : choiceType} R (mu : {meas A}) (eta : {meas B}) := exists w, isLifting R mu eta w.

Lemma lifting_bind {A B C : choiceType} R (c : {meas A}) (f : A -> {meas B}) (g : A -> {meas C}) :
  (forall x, x \in support c -> lifting R (f x) (g x)) ->
  lifting R (x <- c; f x) (x <- c; g x).
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

Lemma id_lifting {A B : choiceType} (R : {meas A} -> {meas B} -> bool) mu eta :
  mass mu = mass eta -> R mu eta -> lifting R mu eta.
  intros; exists (ret (mu, eta)).
  apply/and3P; split.
  rewrite ret_bind //=.
  rewrite ret_bind //=.
  rewrite support_ret all_seq1 //=.
  rewrite H H0 //=.
Qed.
  
Lemma lifting_implies {A B : choiceType} (R : {meas A} -> {meas B} -> bool) (R' : _ -> _ -> bool) :
  (forall mu eta, R mu eta -> R' mu eta) -> forall mu eta, lifting R mu eta -> lifting R' mu eta.
  move => H mu eta; case => l Hl; move/and3P: Hl => [h1 h2 h3].
  rewrite (eqP h1) (eqP h2); apply lifting_bind => x Hx.
  move/andP: (allP h3 x Hx) => [hr hm].
  apply id_lifting; [by apply/eqP | by apply H].
Qed.


Lemma lifting_fmap {A B C D : choiceType} (f1 : A -> C) (f2 : B -> D) (R : {meas C} -> {meas D} -> bool) (mu : {meas A}) (eta : {meas B})
  : lifting (fun mua mub => R (mua <$> f1) (mub <$> f2)) mu eta ->
    lifting R (mu <$> f1) (eta <$> f2).
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
  move/andP: (allP h3 _ hy1) => [hy3 hy4].
  apply/andP; split.
  rewrite support_ret in_cons orbF in hy2; rewrite (eqP hy2) //=.
  rewrite support_ret mem_seq1 in hy2; rewrite (eqP hy2); simpl.

  rewrite !mass_fmap //=.
Qed.

Lemma eq_lifting {A : choiceType} (mu eta : {meas A}) :
  lifting (fun x y => x == y) mu eta -> mu = eta.
  elim => c Hc; simpl in *.
  elim (and3P Hc); simpl => h1 h2 h3.
  rewrite (eqP h1) (eqP h2); apply mbind_eqP => x Hx.
  move/allP: h3.
  move/(_ _ Hx)/andP;elim;move/eqP; done.
Qed.