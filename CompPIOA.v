
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset.

Require Import PIOA Meas Posrat.

Definition prePIOA_comptrans {Act : finType} (P1 P2 : @PIOA Act) (s : [finType of (pQ P1 * pQ P2)]%type) (a : [finType of Act]) : option (Meas ([finType of pQ P1 * pQ P2])%type) :=
  match tr P1 s.1 a, tr P2 s.2 a with
  | Some mu1, Some mu2 => Some (x <- mu1; y <- mu2; ret (x,y))
  | None, Some mu2 => Some (y <- mu2; ret (s.1, y))
  | Some mu1, None => Some (x <- mu1; ret (x, s.2))
  | None, None => None
  end.

Definition comp_prePIOA {Act : finType} (P1 P2 : @PIOA Act) : @prePIOA Act.
  econstructor.
  apply (start P1, start P2).
  instantiate (1 := (prePIOA_comptrans P1 P2)).
  simpl.
  intros.
  destruct s.
  rewrite /prePIOA_comptrans //= in H.
  remember (tr P1 s a) as mu1; remember (tr P2 s0 a) as mu2; symmetry in Heqmu1; symmetry in Heqmu2.
  destruct mu1; destruct mu2; try injection H; try intro; subst.
  eapply isSubdist_bind.
  eapply tr_subDist.
  apply Heqmu1.
  intros; eapply isSubdist_bind.
  eapply tr_subDist.
  apply Heqmu2.
  intros; eapply isSubdist_ret.
  eapply isSubdist_bind; [eapply tr_subDist; apply Heqmu1 | intros; apply isSubdist_ret].
  eapply isSubdist_bind; [eapply tr_subDist; apply Heqmu2 | intros; apply isSubdist_ret].
  congruence.
Defined.

Record Compatible {Act : finType} (P1 P2 : @PIOA Act) :=
  {
    _ : [disjoint (pO P1) & (pO P2)];
    _ : [disjoint (pH P1) & (action P2)];
    _ : [disjoint (pH P2) & (action P1)];
    }.

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

Definition compPIOA {Act : finType} (P1 P2 : @PIOA Act) : Compatible P1 P2 -> @PIOA Act.
  intro; econstructor.
  instantiate (5 := comp_prePIOA P1 P2).
  instantiate (4 := pO P1 :|: pO P2).
  instantiate (3 := pH P1 :|: pH P2).
  instantiate (2 := pTO P1 :|: pTO P2).
  instantiate (1 := pTH P1 :|: pTH P2).
  destruct H.

  constructor.

  apply partition_disjoint.
  have: cover (pTO P1) = pO P1.
    destruct P1.
    destruct TS.
    move: (and3P i0); elim; move/eqP; simpl; done.
  intro Heq; rewrite Heq; clear Heq.

  have: cover (pTO P2) = pO P2.
    destruct P2.
    destruct TS.
    move: (and3P i0); elim; move/eqP; simpl; done.
  intro Heq; rewrite Heq; clear Heq.

  done.
  done.
  destruct P1; destruct TS; done.
  destruct P2; destruct TS; done.

  have: [disjoint pH P1 & pH P2].
  apply/disjointP; move: (disjointP _ _ H0).
  intros.
  have H3 := (elimT _ H2).
  rewrite/action in H3; move/setUP: H3 => H3.
  apply Decidable.not_or in H3; destruct H3.
  move/negP: H4; done.
  intro.

  apply partition_disjoint.


  have: cover (pTH P1) = pH P1.
    destruct P1.
    destruct TS.
    move: (and3P i1); elim; move/eqP; simpl; done.
  intro Heq; rewrite Heq; clear Heq.

  have: cover (pTH P2) = pH P2.
    destruct P2.
    destruct TS.
    move: (and3P i1); elim; move/eqP; simpl; done.
  intro Heq; rewrite Heq; clear Heq.
  done.
  done.


  destruct P1; destruct TS; done.
  destruct P2; destruct TS; done.

  intros.
  rewrite /actionDeterm.

  intros.
  rewrite /enabled.
  simpl.
  admit.

  instantiate (1 := pI P1 :|: pI P2).
  apply/trivIsetP; intros.
  admit.
  admit.
  admit.
Admitted.
