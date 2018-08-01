
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA2 Meas Posrat Lems.

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
    _ : forall x y, x \in pTO P1 -> y \in pTO P2 -> [disjoint x & y];
    _ : forall x y, x \in pTH P1 -> y \in action P2 -> [disjoint x & y];
    _ : forall x y, x \in pTH P2 -> y \in action P1 -> [disjoint x & y];
    }.



Lemma notsetU : forall {T : finType} {s1 s2 : {set T}} {x},
                          (x \notin s1 :|: s2) = ((x \notin s1) && (x \notin s2)).
intros.
rewrite in_setU negb_or; done.
Qed.

Lemma disjoint_setD {T : finType} (s1 s2 s3 : {set T}) :
  [disjoint s1 & s3] ->
  [disjoint (s1 :\: s2) & s3].
  move/disjointP; intro H; apply/disjointP; intros.
  apply H.
  move/setDP: H0; elim; done.
Qed.

Definition compPIOA {Act : finType} (P1 P2 : @PIOA Act) : Compatible P1 P2 -> @PIOA Act.
  intro H; destruct H.
  econstructor.
  instantiate (1 := pTH P1 :|: pTH P2).
  instantiate (1 := pTO P1 :|: pTO P2).
  instantiate (1 := (pI P1 :|: pI P2) :\: (cover (pTO P1 :|: pTO P2))).
  econstructor.
  move=> x Hx.

  intros; apply/disjointP; intros.
  move/setDP: H2; elim; intros.
  move: H3; apply contraLR; rewrite !negbK.
  intro; apply/bigcupP; exists x; done.
  intros.
  apply disjoint_setD.

  apply/disjointP; intros.
  move/setUP: H2; elim.
  move/setUP: H3; elim; intros.
  destruct (actionDisjoint P1).
  move/disjointP: (H5 _ H3).
  intro He; apply He; done.
  move: (H0 _ _ H3 (pI_in_action P2)); rewrite disjoint_sym; move/disjointP.
  intro Hd; apply Hd; done.

  move/setUP: H3; elim; intros.
  move: (H1 _ _ H3 (pI_in_action P1)); rewrite disjoint_sym; move/disjointP.
  intro Hd; apply Hd; done.

  destruct (actionDisjoint P2).
  move/disjointP: (H5 _ H3); intro Hd; apply Hd; done.

  move=> x y; move/setUP; elim; intro; move/setUP; elim; intro.

  destruct (actionDisjoint P1).
  apply H6; done.

  rewrite disjoint_sym; apply H1.
  done.
  apply tO_in_action; done.
  rewrite disjoint_sym; apply H0.
  done.
  apply tO_in_action; done.
  destruct (actionDisjoint P2).
  apply H6; done.

  move=> x y; move/setUP; elim; intro; move/setUP; elim; intros.
  destruct (actionDisjoint P1).
  apply H8; done.
  apply H; done.
  rewrite disjoint_sym; apply H; done.
  destruct (actionDisjoint P2); apply H8; done.

  move=> x y; move/setUP; elim; intro; move/setUP; elim; intros.
  destruct (actionDisjoint P1).
  apply H9; done.
  apply H0.
  done.
  apply tH_in_action; done.
  rewrite disjoint_sym; apply H0.
  done.
  apply tH_in_action; done.

  destruct (actionDisjoint P2); apply H9; done.

  instantiate (1 := comp_prePIOA P1 P2).
  intros; rewrite /actionDeterm.
  intros; rewrite /enabled //= /prePIOA_comptrans.
  move/setUP: H2; elim; move/setUP; elim; intros.

  remember (tr P1 s.1 x) as mu1; remember (tr P1 s.1 y) as mu2; destruct mu1; destruct mu2.

  have Hc := pActionDeterm P1 T _ _.


  exfalso.
  apply/contraT.

  Search "False" "false".
  exfalso.
  apply/negP.
  admit.

  exfalso; apply/negP. apply Hc.
  apply Hc.

  Check (pActionDeterm P1).
  exfalso; apply (pActionDeterm P1 T).


  