
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat Lems.

Definition prePIOA_comptrans {Act : finType} (P1 P2 : @PIOA Act) (s : [finType of (pQ P1 * pQ P2)]%type) (a : [finType of Act]) : option (Meas ([finType of pQ P1 * pQ P2])%type) :=
  match tr P1 s.1 a, tr P2 s.2 a with
  | Some mu1, Some mu2 => Some (x <- mu1; y <- mu2; ret (x,y))
  | None, Some mu2 => if a \notin (cover (action P1)) then Some (y <- mu2; ret (s.1, y)) else None
  | Some mu1, None => if a \notin (cover (action P2)) then Some (x <- mu1; ret (x, s.2)) else None
  | None, None => None
  end.

Lemma prePIOA_comptrans_subdist {Act : finType} (P1 P2 : @PIOA Act) s a mu : prePIOA_comptrans P1 P2 s a = Some mu -> isSubdist mu.
  simpl.
  intros.
  destruct s.
  rewrite /prePIOA_comptrans //= in H.
  remember (tr P1 s a) as mu1; remember (tr P2 s0 a) as mu2; symmetry in Heqmu1; symmetry in Heqmu2.
  destruct mu1; destruct mu2; intros; subst.
  injection H; intros; subst; dsubdist; intros; dsubdist; intros; dsubdist.
  caseOn (a \notin cover (action P2)); intro Hc; [rewrite Hc in H | rewrite (negbTE Hc) in H].
  injection H; intros; subst; dsubdist; intros; dsubdist; intros; dsubdist.
  done.
  caseOn (a \notin cover (action P1)); intro Hc; [rewrite Hc in H | rewrite (negbTE Hc) in H].
  injection H; intros; subst; dsubdist; intros; dsubdist; intros; dsubdist.
  done.
  done.
Qed.


Definition comp_prePIOA {Act : finType} (P1 P2 : @PIOA Act) := mkPrePIOA Act ([finType of (pQ P1 * pQ P2)%type]) (start P1, start P2) (prePIOA_comptrans P1 P2) (prePIOA_comptrans_subdist P1 P2).

Record Compatible {Act : finType} (P1 P2 : @PIOA Act) :=
  {
    _ : [forall (x | x \in pTO P1), [forall (y | y \in pTO P2), [disjoint x & y]]];
    _ : [forall (x | x \in pTH P1), [forall (y | y \in action P2), [disjoint x & y]]];
    _ : [forall (x | x \in pTH P2), [forall (y | y \in action P1), [disjoint x & y]]];
    }.


Lemma compatible_sym {A : finType} (P1 P2 : @PIOA A) :
  Compatible P1 P2 -> Compatible P2 P1.
  case => h1 h2 h3; constructor.
  apply/forall_inP => x Hx; apply/forall_inP => y Hy;
  move: (forall_inP (forall_inP h1 y Hy) x Hx); by rewrite disjoint_sym.

  apply/forall_inP => x Hx; apply/forall_inP => y Hy;
  move: (forall_inP (forall_inP h3 x Hx) y Hy); by rewrite disjoint_sym.

  apply/forall_inP => x Hx; apply/forall_inP => y Hy;
  move: (forall_inP (forall_inP h2 x Hx) y Hy); by rewrite disjoint_sym.
Defined.

Lemma notsetU : forall {T : finType} {s1 s2 : {set T}} {x},
                          (x \notin s1 :|: s2) = ((x \notin s1) && (x \notin s2)).
intros.
rewrite in_setU negb_or; done.
Defined.

Lemma notincover : forall {T : finType} (x : T) (s : {set {set T}}), 
                            (x \notin (cover s)) =
                            [forall t, (t \in s) ==> (x \notin t)].
  intros; caseOn (x \in cover s); intros.
  rewrite H //=.
  symmetry; apply/forallP.
  intro.
  move/bigcupP: H; elim; intros.
  move/implyP: (H0 x0).
  intro Hc; rewrite (negbTE (Hc H)) in H1; done.
  rewrite H; symmetry.
  apply/forallP; intros.
  move/bigcupP: H.
  intros.
  apply/implyP; intro.
  caseOn (x \in x0).
  intro; exfalso; apply H.
  exists x0; done.
  done.
Defined.

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
  3: {
  instantiate (1 := comp_prePIOA P1 P2).
  instantiate (1 := (pI P1 :|: pI P2) :\: (cover (pTO P1 :|: pTO P2))).
  move=> s x; move/setDP; elim; move/setUP; elim; intros.
  rewrite /enabled.

  move/enabledP: (inputEnabled P1 s.1 x H0); elim.
  simpl; rewrite /prePIOA_comptrans; intros.
  rewrite H2.
  caseOn (x \in cover (action P2)); intro.
  rewrite/action /cover !bigcup_setU in H3.
  move/setUP: H3; elim; intros.
  move/setUP: H3; elim; intros.
  move/bigcupP: H3; elim; intros.
  rewrite in_set in H3.
  rewrite (eqP H3) in H4.
  move/enabledP: (inputEnabled P2 s.2 x H4).
  elim; intros.
  rewrite H5; done.
  rewrite notincover in H1.
  move/forallP: H1; intros.
  move/bigcupP: H3; elim; intros.
  move/implyP: (H1 x1).
  intros.
  rewrite H4 in H5.
  simpl in H5.
  have: false.
  apply H5.
  apply/setUP; right; done.
  done.

  destruct H.
  have: false.
  move/bigcupP: H3; elim; intros.
  move/disjointP: (forall_inP (forall_inP H5 _ H3) _ (pI_in_action P1)).
  move/(_ _ H6); by rewrite H0.
  done.
  rewrite H3; destruct (tr P2 s.2 x); done.

  simpl; rewrite /enabled //= /prePIOA_comptrans.
  move/enabledP: (inputEnabled P2 s.2 x H0); elim; intros.
  rewrite H2.
  caseOn (x \in cover (action P1)).
  rewrite /cover /action !bigcup_setU.
  move/setUP; elim.
  move/setUP; elim.
  move/bigcupP; elim; intro; rewrite in_set.
  move/eqP; intro; subst.
  intro HPi; move/enabledP: (inputEnabled P1 s.1 x HPi).
  elim; intros mu Hmu; rewrite Hmu.
  done.
  move/bigcupP.
  elim; intros.
  move/bigcupP: H1.
  elim.
  exists x1.
  apply/setUP; left; done.
  done.
  intro.
  destruct H.
  move/bigcupP: H3; elim; intros.
  move/disjointP: (forall_inP (forall_inP H4 _ H3) _ (pI_in_action P2)).
  move/(_ _ H6); by rewrite H0.

  move=> Hr; rewrite Hr.
  by destruct (tr P1 s.1 x).
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
  move: (forall_inP (forall_inP H1 _ H2) _ (pI_in_action P1)); rewrite disjoint_sym; move/disjointP.
  move/(_ _ H3); done.

  move/setUP: H2; elim; intros.
  move: (forall_inP (forall_inP H0 _ H2) _ (pI_in_action P2)); rewrite disjoint_sym; move/disjointP.
  move/(_ _ H3); done.

  destruct (actionDisjoint P2).
  move/disjointP: (H5 _ H2); intro Hd; apply Hd; done.

  move=> x y; move/setUP; elim; intro; move/setUP; elim; intro.

  destruct (actionDisjoint P1).
  apply H6; done.

  rewrite disjoint_sym;
    apply: (forall_inP (forall_inP H1 _ _)).
  done.
  apply tO_in_action; done.
  rewrite disjoint_sym; apply: (forall_inP (forall_inP H0 _ _)).
  done.
  apply tO_in_action; done.
  destruct (actionDisjoint P2).
  apply H6; done.

  move=> x y; move/setUP; elim; intro; move/setUP; elim; intros.
  destruct (actionDisjoint P1).
  apply H8; done.
  apply: (forall_inP (forall_inP H _ _)); done.

  rewrite disjoint_sym; apply: (forall_inP (forall_inP H _ _)); done.
  destruct (actionDisjoint P2); apply H8; done.

  move=> x y; move/setUP; elim; intro; move/setUP; elim; intros.
  destruct (actionDisjoint P1).
  apply H9; done.
  apply: (forall_inP (forall_inP H0 _ _)).
  done.
  apply tH_in_action; done.
  rewrite disjoint_sym; apply: (forall_inP (forall_inP H0 _ _)).
  done.
  apply tH_in_action; done.


  destruct (actionDisjoint P2); apply H9; done.

  (* *** Action determinism *** *)
  intros; rewrite /actionDeterm.
  intros.
  apply/andP.
  intro.
  destruct H4.
  move/setUP: H0; elim; move/setUP; elim.


  move/enabledP: H4; elim; intros.
  move/enabledP: H5; elim; intros.
  rewrite //= in H0; rewrite /comp_prePIOA /prePIOA_comptrans in H0.
  rewrite //= in H5; rewrite /comp_prePIOA /prePIOA_comptrans in H5.
  have tin : T \in pTO P1 :|: pTH P1.
  apply/setUP; left;done.

  have Hc:= pActionDeterm P1 T tin s.1 x y H1 H2 H3.

  have: x \in cover (action P1).
  apply/bigcupP; exists T; rewrite /action. apply/setUP; left; apply/setUP; right; done.
  done.
  intro xincov.

  have: y \in cover (action P1).
  apply/bigcupP; exists T; rewrite /action. apply/setUP; left; apply/setUP; right; done.
  done.
  intro yincov.

  remember (tr P1 s.1 x) as mu1; symmetry in Heqmu1; destruct mu1;
  remember (tr P1 s.1 y) as mu2; symmetry in Heqmu2; destruct mu2.
  rewrite /enabled Heqmu1 Heqmu2 in Hc; done.

  rewrite yincov //= in H5; destruct (tr P2 s.2 y); done.
  rewrite xincov //= in H0; destruct (tr P2 s.2 x); done.
  rewrite yincov //= in H5; destruct (tr P2 s.2 y); done.


  move/enabledP: H4; elim; intros.
  move/enabledP: H5; elim; intros.
  rewrite //= in H0; rewrite /comp_prePIOA /prePIOA_comptrans in H0.
  rewrite //= in H5; rewrite /comp_prePIOA /prePIOA_comptrans in H5.
  have tin : T \in pTO P2 :|: pTH P2.
  apply/setUP; left; done.

  have Hc:= pActionDeterm P2 T tin s.2 x y H1 H2 H3.

  have: x \in cover (action P2).
  apply/bigcupP; exists T; rewrite /action. apply/setUP; left; apply/setUP; right; done.
  done.
  intro xincov.

  have: y \in cover (action P2).
  apply/bigcupP; exists T; rewrite /action. apply/setUP; left; apply/setUP; right; done.
  done.
  intro yincov.

  remember (tr P2 s.2 x) as eta1; symmetry in Heqeta1; destruct eta1;
  remember (tr P2 s.2 y) as eta2; symmetry in Heqeta2; destruct eta2.
  rewrite /enabled Heqeta1 Heqeta2 in Hc; done.

  rewrite yincov //= in H5; destruct (tr P1 s.1 y); done.
  rewrite xincov //= in H0; destruct (tr P1 s.1 x); done.
  rewrite yincov //= in H5; destruct (tr P1 s.1 y); done.


  move/enabledP: H4; elim; intros.
  move/enabledP: H5; elim; intros.
  rewrite //= in H0; rewrite /comp_prePIOA /prePIOA_comptrans in H0.
  rewrite //= in H5; rewrite /comp_prePIOA /prePIOA_comptrans in H5.
  have tin : T \in pTO P1 :|: pTH P1.
  apply/setUP; right;done.

  have Hc:= pActionDeterm P1 T tin s.1 x y H1 H2 H3.

  have: x \in cover (action P1).
  apply/bigcupP; exists T; rewrite /action. apply/setUP; right. done.
  done.
  intro xincov.

  have: y \in cover (action P1).
  apply/bigcupP; exists T; rewrite /action. apply/setUP; right; done.
  done.
  intro yincov.

  remember (tr P1 s.1 x) as mu1; symmetry in Heqmu1; destruct mu1;
  remember (tr P1 s.1 y) as mu2; symmetry in Heqmu2; destruct mu2.
  rewrite /enabled Heqmu1 Heqmu2 in Hc; done.

  rewrite yincov //= in H5; destruct (tr P2 s.2 y); done.
  rewrite xincov //= in H0; destruct (tr P2 s.2 x); done.
  rewrite yincov //= in H5; destruct (tr P2 s.2 y); done.


  move/enabledP: H4; elim; intros.
  move/enabledP: H5; elim; intros.
  rewrite //= in H0; rewrite /comp_prePIOA /prePIOA_comptrans in H0.
  rewrite //= in H5; rewrite /comp_prePIOA /prePIOA_comptrans in H5.
  have tin : T \in pTO P2 :|: pTH P2.
  apply/setUP; right;done.

  have Hc:= pActionDeterm P2 T tin s.2 x y H1 H2 H3.

  have: x \in cover (action P2).
  apply/bigcupP; exists T; rewrite /action. apply/setUP; right. done.
  done.
  intro xincov.

  have: y \in cover (action P2).
  apply/bigcupP; exists T; rewrite /action. apply/setUP; right; done.
  done.
  intro yincov.

  remember (tr P2 s.2 x) as eta1; symmetry in Heqeta1; destruct eta1;
  remember (tr P2 s.2 y) as eta2; symmetry in Heqeta2; destruct eta2.
  rewrite /enabled Heqeta1 Heqeta2 in Hc; done.

  rewrite yincov //= in H5; destruct (tr P1 s.1 y); done.
  rewrite xincov //= in H0; destruct (tr P1 s.1 x); done.
  rewrite yincov //= in H5; destruct (tr P1 s.1 y); done.


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


Definition CompPIOA {A : finType} (P1 P2 : @PIOA A) := Compatible P1 P2.

Definition comp_of_ppair {A : finType} (P1 P2 : @PIOA A) : Compatible P1 P2 -> @PIOA A.
  apply compPIOA.
Defined.

Coercion comp_of_ppair : Compatible >-> PIOA.

Notation "P1 ||| P2" := (CompPIOA P1 P2) (at level 60).

Lemma compPIOA_irrel {A : finType} (P1 P2 : @PIOA A) (h1 h2 : P1 ||| P2) : h1 = h2.
  destruct h1.
  destruct h2.
  have: [/\ (i = i2), (i0 = i3) & (i1 = i4)].
  split; apply eq_irrelevance.
  case; intros; subst; done.
Defined.
