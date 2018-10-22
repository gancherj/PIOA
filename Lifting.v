
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
Require Import Posrat Premeas Meas Program.

Check and3P.
Check forallP.
Check allP.

Definition isLifting {A B : choiceType} (R : Meas A -> Meas B -> bool) (mu : Meas A) (eta : Meas B) (w : Meas [choiceType of (Meas A) * (Meas B)]) :=
  [&& (mu == (p <- w; p.1)), (eta == (p <- w; p.2)) & (all (fun p => R p.1 p.2) (measSupport w))].

Definition lifting {A B : choiceType} R (mu : Meas A) (eta : Meas B) := exists w, isLifting R mu eta w.


Lemma liftingBind {A B C : choiceType} R (c : Meas A) (f : A -> Meas B) (g : A -> Meas C) :
  (forall x, lifting R (f x) (g x)) ->
  lifting R (x <- c; f x) (x <- c; g x).
  move=> H.
  exists (x <- c; (xchoose (H x))).
  apply/and3P; split.
  rewrite bindAssoc; apply/eqP/MeasP => h; rewrite !integ_measBind.
  apply integ_eq_fun => x.
  have H2 := xchooseP (H x); move/and3P: H2; elim => h1 h2 h3.
  rewrite -(eqP h1); done.

  rewrite bindAssoc; apply/eqP/MeasP => h; rewrite !integ_measBind.
  apply integ_eq_fun => x.
  have H2 := xchooseP (H x); move/and3P: H2; elim => h1 h2 h3.
  rewrite -(eqP h2); done.

  apply/allP => x Hx.
  elim (measSupport_bind _ _ _ Hx) => x0 [h1 h2].
  have H2 := xchooseP (H x0); move/and3P: H2; elim => h3 h4 h5.
  move/allP: h5 => h5.
  apply h5.
  done.
Qed.


Lemma liftingBind_dep {A B C : choiceType} R (c : Meas A) (f : A -> Meas B) (g : A -> Meas C) :
  (forall x, x \in measSupport c -> lifting R (f x) (g x)) ->
  lifting R (x <- c; f x) (x <- c; g x).
  move => H.
  exists (measBind_dep c (fun x p => xchoose (H x p))).
  apply/and3P; split.

  rewrite /measBind_dep bindAssoc.
  apply/eqP/MeasP => h; rewrite !integ_measBind.
  apply integ_eq_fun_dep => x Hx.
  rewrite odflt_depP.

  have H2 := xchooseP (H x Hx); move/and3P: H2; elim => h1 h2 h3.
  rewrite -(eqP h1); done.

  rewrite /measBind_dep bindAssoc.
  apply/eqP/MeasP => h; rewrite !integ_measBind.
  apply integ_eq_fun_dep => x Hx.
  rewrite odflt_depP.
  have H2 := xchooseP (H x Hx); move/and3P: H2; elim => h1 h2 h3.
  rewrite -(eqP h2); done.

  apply/allP => x.
  move/measSupport_bind_dep; elim => y; elim => h hin.

  have H2 := xchooseP (H y h); move/and3P: H2; elim => h1 h2 h3.
  move/allP: h3 => h3.
  apply h3.
  done.
Qed.