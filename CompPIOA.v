
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA2 Meas Posrat.

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
    _ : [disjoint (cover (pTO P1)) & (cover (pTO P2))];
    _ : [disjoint (cover (pTH P1)) & (action P2)];
    _ : [disjoint (cover (pTH P2)) & (action P1)];
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

Lemma notsetU : forall {T : finType} {s1 s2 : {set T}} {x},
                          (x \notin s1 :|: s2) = ((x \notin s1) && (x \notin s2)).
intros.
rewrite in_setU negb_or; done.
Qed.

  Lemma compPIOA_trivIset {A : finType} (P1 P2 : @PIOA A) (H : Compatible P1 P2) :
    trivIset
    ((pI P1 :|: pI P2) :\: (cover (pTO P1) :|: cover (pTO P2)) |: (pTO P1 :|: pTO P2)
     :|: (pTH P1 :|: pTH P2)).
    admit.
    Admitted.

  Lemma compPIOA_actionDeterm {A : finType} (P1 P2 : @PIOA A) T :T \in pTO P1 :|: pTO P2 :|: (pTH P1 :|: pTH P2) -> actionDeterm (comp_prePIOA P1 P2) T.
    admit.
    Admitted.

  Lemma compPIOA_inputEnabled {A : finType} (P1 P2 : @PIOA A) (H : Compatible P1 P2) :
  forall (s : pQ (comp_prePIOA P1 P2)) (x : A),
  x \in (pI P1 :|: pI P2) :\: (cover (pTO P1) :|: cover (pTO P2)) ->
  enabled (comp_prePIOA P1 P2) s x   .
  Admitted.

  Lemma compPIOA_actSetValid {Act : finType} (P1 P2 : @PIOA Act) :
     forall (s : pQ (comp_prePIOA P1 P2)) (x : Act),
  enabled (comp_prePIOA P1 P2) s x ->
  x
    \in (pI P1 :|: pI P2) :\: (cover (pTO P1) :|: cover (pTO P2))
        :|: (cover (pTO P1 :|: pTO P2) :|: cover (pTH P1 :|: pTH P2)).
    Admitted.


Definition compPIOA {Act : finType} (P1 P2 : @PIOA Act) : Compatible P1 P2 -> @PIOA Act.
  intro; econstructor.
  instantiate (3 := (pI P1 :|: pI P2) :\: (cover (pTO P1) :|: cover (pTO P2))).
  instantiate (2 := pTO P1 :|: pTO P2).
  instantiate (1 := pTH P1 :|: pTH P2).
  apply compPIOA_trivIset.
  done.

  apply compPIOA_actionDeterm.

  apply compPIOA_inputEnabled; done.

  apply compPIOA_actSetValid.
Defined.


