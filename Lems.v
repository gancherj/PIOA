From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import fset.

Lemma EM (b : bool) : forall (P : Type), (b -> P) -> (~~ b -> P) -> P.
  destruct b; intros P H H0; [apply H | apply H0]; done.
Defined.

Lemma bcase (b1 b2 : bool) : forall (P : Type), (b1 -> P) -> (b2 -> P) -> (b1 || b2 -> P).
  destruct b1, b2; intros P H H0.
  simpl; apply H.
  simpl; apply H.
  simpl; apply H0.
  simpl; apply H.
Defined.

Print bcase.

Ltac caseOn b := apply (EM b).

Lemma fdisjointP {T : choiceType} (P Q : {fset T}) :
  reflect (forall x, x \in P ->  x \notin Q) (fdisj P Q).
  apply/(iffP idP).
  rewrite /fdisj.
  move/eqP => eq0.
  intros.
  apply/contraT.
  rewrite negbK; intros.

  have: x \in P `&` Q.
  rewrite in_fsetI; rewrite H H0 //=.
  intros.
  rewrite eq0 in x0.
  rewrite in_fset0 in x0; done.

  intros.
  rewrite /fdisj; apply/eqP; apply fset_ext => x.
  rewrite in_fset0.
  apply/negP => Hc.
  rewrite in_fsetI in Hc.
  caseOn (x \in P) => Hx.
  rewrite (negbTE (H _ Hx)) andbF in Hc; done.
  rewrite (negbTE Hx) in Hc; done.
Qed.

