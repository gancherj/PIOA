
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

Lemma prePIOA_comptrans_subdist {Act : finType} (P1 P2 : @PIOA Act) : forall s a mu,
    prePIOA_comptrans P1 P2 s a = Some mu ->
    isSubdist mu.
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
Qed.

Check mkPrePIOA.

Definition comp_prePIOA {Act : finType} (P1 P2 : @PIOA Act) := mkPrePIOA Act ([finType of (pQ P1 * pQ P2)%type]) (start P1, start P2) (prePIOA_comptrans P1 P2) (prePIOA_comptrans_subdist P1 P2).

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


  intro; econstructor.
  (* *** input enabledness *** *)
  2: {
  instantiate (1 := comp_prePIOA P1 P2).
  instantiate (1 := (pI P1 :|: pI P2) :\: (cover (pTO P1 :|: pTO P2))).
  move=> s x; move/setDP; elim; move/setUP; elim; intros.
  rewrite /enabled.

  have Hi := inputEnabled P1 s.1 x H0.
  simpl; rewrite /prePIOA_comptrans.
  have: exists mu, tr P1 s.1 x = Some mu.
  rewrite /enabled in Hi; destruct (tr P1 s.1 x).
  eexists; done.
  done.
  elim; intros.
  rewrite H2.
  destruct (tr P2 s.2 x); done.

  have Hi := inputEnabled P2 s.2 x H0.
  simpl; rewrite /prePIOA_comptrans.
  have: exists mu, tr P2 s.2 x = Some mu.
  rewrite /enabled in Hi; destruct (tr P2 s.2 x).
  eexists; done.
  done.
  rewrite /enabled //= /prePIOA_comptrans.
  elim; intros.
  rewrite H2.
  destruct (tr P1 s.1 x); done.
  }


  instantiate (1 := pTH P1 :|: pTH P2).
  instantiate (1 := pTO P1 :|: pTO P2).

  destruct H.
  constructor.

  move=> x Hx.

  intros; apply/disjointP; intros.
  move/setDP: H2; elim; intros.
  move: H3; apply contraLR; rewrite !negbK.
  intro; apply/bigcupP; exists x; done.
  intros.
  apply disjoint_setD.

  apply/disjointP; intros.
  move/setUP: H3; elim.
  move/setUP: H2; elim; intros.
  destruct (actionDisjoint P1).
  move/disjointP: (H5 _ H2).
  intro He; apply He; done.
  move: (H1 _ _ H2 (pI_in_action P1)); rewrite disjoint_sym; move/disjointP.
  intro Hd; apply Hd; done.

  move/setUP: H2; elim; intros.
  move: (H0 _ _ H2 (pI_in_action P2)); rewrite disjoint_sym; move/disjointP.
  intro Hd; apply Hd; done.

  destruct (actionDisjoint P2).
  move/disjointP: (H5 _ H2); intro Hd; apply Hd; done.

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

  (* *** Action determinism *** *)



  (* action validity *)

  rewrite /enabled //= /prePIOA_comptrans.
  intros.
  remember (tr P1 s.1 x) as mu; destruct mu.
  have: enabled P1 s.1 x.
  rewrite /enabled -Heqmu; done.
  intro.
  Check actSetValid.
  move/setUP: (actSetValid P1 s.1 x x0); elim. move/setUP; elim.
  remember (x \in cover (pTO P2)); symmetry in Heqb; destruct b.
  intro; apply/setUP; left; apply/setUP; right.
  rewrite /cover.
  rewrite bigcup_setU.
  apply/setUP; right.
  apply Heqb.
  intro; apply/setUP; left; apply/setUP; left.
  apply/setDP; split.
  apply/setUP; left; done.
  rewrite /cover bigcup_setU notsetU.
  rewrite Heqb.
  rewrite //= andbT.
  apply/bigcupP; elim.
  intros.
  destruct (actionDisjoint P1).
  move: (H4 _ H2).
  move/disjointP.
  intro Hc; move: (Hc _ H1).
  move/negP.
  intros Hcc; apply Hcc; done.

  intro; apply/setUP; left; apply/setUP; right.
  rewrite /cover bigcup_setU; apply/setUP; left; done.
  intro; apply/setUP; right.
  rewrite /cover bigcup_setU; apply/setUP; left; done.
  have: enabled P2 s.2 x.
  rewrite /enabled; destruct (tr P2 s.2 x); done.
  intro.

  move/setUP: (actSetValid P2 s.2 x x0); elim. move/setUP; elim.
  remember (x \in cover (pTO P1)); symmetry in Heqb; destruct b.
  intro; apply/setUP; left; apply/setUP; right.
  rewrite /cover.
  rewrite bigcup_setU.
  apply/setUP; left.
  apply Heqb.
  intro; apply/setUP; left; apply/setUP; left.
  apply/setDP; split.
  apply/setUP; right; done.
  rewrite /cover bigcup_setU notsetU.
  rewrite Heqb.
  simpl.
  apply/bigcupP; elim.
  intros.
  destruct (actionDisjoint P2).
  move: (H4 _ H2).
  move/disjointP.
  intro Hc; move: (Hc _ H1).
  move/negP.
  intros Hcc; apply Hcc; done.

  intro; apply/setUP; left; apply/setUP; right.
  rewrite /cover bigcup_setU; apply/setUP; right; done.
  intro; apply/setUP; right.
  rewrite /cover bigcup_setU; apply/setUP; right; done.
Defined.