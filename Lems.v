From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Lemma disjointP {T : finType} (P Q : {set T}) :
  reflect (forall x, x \in P ->  x \notin Q) ([disjoint P & Q]).
  apply/(iffP idP).
  rewrite -setI_eq0.
  intros.
  apply/contraT.
  rewrite negbK; intros.
  have: x \in P :&: Q.
  apply/setIP; done.
  intros.
  rewrite (eqP H) in x0.
  rewrite in_set0 in x0; done.

  intros.
  rewrite -setI_eq0.
  apply/eqP/setP; move=> z.
  apply/setIP.
  rewrite in_set0.
  elim.
  intros.
  have HC := H _ H0.
  move/negP: HC.
  done.
Qed.

Lemma partition_disjoint {T : finType} (P Q : {set {set T}}) (A B : {set T}) :
  [disjoint (cover P) & (cover Q)] ->
  [disjoint A & B] ->
  partition P A ->
  partition Q B ->
  partition (P :|: Q) (A :|: B).

rewrite /partition.
intros.
move/and3P: H1 => [H11 H12 H13].
move/and3P: H2 => [H21 H22 H23].
apply/and3P; split.
rewrite /cover bigcup_setU.
rewrite /cover in H11; rewrite (eqP H11).
rewrite /cover in H21; rewrite (eqP H21).
done.
apply/trivIsetP.
move=> x y Hx Hy Hneq.
move/setUP: Hx => [Hx1 | Hx2].
move/setUP: Hy => [Hy1 | Hy2].
move/trivIsetP: H12.
intros.
apply H12; done.

apply/disjointP.
intros.
move/disjointP: H => H.
apply/contraT; rewrite negbK; intros.
have: x0 \in cover P.
apply/bigcupP; exists x; done.
have: x0 \in cover Q.
apply/bigcupP; exists y; done.
intros.
have HC := H _ x2.
move/negP: HC; elim; done.

move/setUP: Hy => [Hy1 | Hy2].

apply/disjointP.
intros.
move/disjointP: H => H.
apply/contraT; rewrite negbK; intros.
have: x0 \in cover P.
apply/bigcupP; exists y; done.
have: x0 \in cover Q.
apply/bigcupP; exists x; done.
intros.
have HC := H _ x2.
move/negP: HC; elim; done.

move/trivIsetP: H22.
intros.
apply H22; done.

apply/setUP; elim; intros.
move/negP: H13; done.
move/negP: H23; done.
Qed.

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