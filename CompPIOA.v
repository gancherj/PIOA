
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat Lems.
Require Import fset.

Definition prePIOA_comptrans {Act} (P1 P2 : @PIOA Act) (s : [finType of (pQ P1 * pQ P2)]%type) (a : [choiceType of Act]) : option (Meas ([choiceType of pQ P1 * pQ P2])%type) :=
  match tr P1 s.1 a, tr P2 s.2 a with
  | Some mu1, Some mu2 => Some (x <- mu1; y <- mu2; ret (x,y))
  | None, Some mu2 => if a \notin (cover (action P1)) then Some (y <- mu2; ret (s.1, y)) else None
  | Some mu1, None => if a \notin (cover (action P2)) then Some (x <- mu1; ret (x, s.2)) else None
  | None, None => None
  end.

Lemma prePIOA_comptrans_subdist {Act } (P1 P2 : @PIOA Act) s a mu : prePIOA_comptrans P1 P2 s a = Some mu -> isSubdist mu.
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


Definition comp_prePIOA {Act : choiceType} (P1 P2 : @PIOA Act) := mkPrePIOA Act ([finType of (pQ P1 * pQ P2)%type]) (start P1, start P2) (prePIOA_comptrans P1 P2) (prePIOA_comptrans_subdist P1 P2).

Record Compatible {Act : choiceType} (P1 P2 : @PIOA Act) :=
  {
    _ : forall x y, x \in pTO P1 -> y \in pTO P2 -> fdisj x y;
    _ : forall x y, x \in pTH P1 -> y \in action P2 -> fdisj x y;
    _ : forall x y, x \in pTH P2 -> y \in action P1 -> fdisj x y;
    }.


Lemma compatible_sym {A : choiceType} (P1 P2 : @PIOA A) :
  Compatible P1 P2 -> Compatible P2 P1.
  intros.
  destruct H.
  constructor.
  intros; rewrite /fdisj fsetIC; apply H; done.
  intros; apply H1; done.
  intros; apply H0; done.
Qed.

Lemma notfsetU : forall {T : choiceType} {s1 s2 : {fset T}} {x},
                          (x \notin s1 `|` s2) = ((x \notin s1) && (x \notin s2)).
intros.
rewrite in_fsetU negb_or; done.
Qed.

Lemma notincover : forall {T : choiceType} (x : T) (s : {fset {fset T}}), 
                            (x \notin (cover s)) -> 
                            ((forall t, (t \in s) -> (x \notin t))).
  intros.
  apply/contraT.
  rewrite negbK; intros.
  move/cupP: H.
  elim.
  exists t.
  rewrite H0 H1 //=.
Qed.

Lemma disjoint_setD {T : choiceType} (s1 s2 s3 : {fset T}) :
  fdisj s1 s3 ->
  fdisj (s1 `\` s2) s3.

  move/fdisjointP; intro H; apply/fdisjointP; intros.
  apply H.
  rewrite in_fsetD in H0; move/andP: H0; elim; done.
Qed.

Lemma disjoint_sym {T : choiceType} (s1 s2 : {fset T}) :
  fdisj s1 s2 = fdisj s2 s1.
  rewrite /fdisj fsetIC; done.
Qed.



Lemma bigcup_fsetU : forall (T I : choiceType) (A B : {fset I}) (F : I -> {fset T}),
       \bigcup_(i in (A `|` B)) F i = \bigcup_(i in A) F i `|` \bigcup_(i in B) F i.
  intros.
  apply fset_ext => x.
  caseOn (x \in \bigcup_(i in A `|` B) F i).
  intros.
  rewrite H.
  move/cupP: H; elim.
  move => x0 /andP ; elim.
  move/fsetUP; elim; intros; symmetry; apply/fsetUP; [left | right]; apply/cupP; exists x0; move/andP: H0; elim; intros; rewrite H H1 //=.
  intros.
  rewrite (negbTE H).
  symmetry;
  apply/fsetUP.
  elim.
  move/cupP; elim; intros.
  move/cupP: H; elim; intros.
  exists x0.
  move/andP: H0; elim; intros.
  move/andP: H0; elim; intros.
  rewrite in_fsetU.
  rewrite H andTb H1; done.
  move/cupP: H; intros.
  move/cupP: H0; elim; intros.
  apply H.
  exists x0.
  move/andP: H0; elim; intros.
  move/andP: H1; elim; intros.
  rewrite in_fsetU H0 orbT H2; done.
Qed.

  Lemma coverU {X : choiceType} (F G : {fset {fset X}}) :
    cover (F `|` G) = cover F `|` cover G.
    rewrite /cover bigcup_fsetU //=.
  Qed.

Definition compPIOA {Act : choiceType} (P1 P2 : @PIOA Act) : Compatible P1 P2 -> @PIOA Act.


  intro; econstructor.

  (* *** input enabledness *** *)
  3: {
  instantiate (1 := comp_prePIOA P1 P2).
  instantiate (1 := (pI P1 `|` pI P2) `\` (cover (pTO P1 `|` pTO P2))).
  move=> s x; rewrite in_fsetD; move/andP; elim; move/fsetUP; elim; intros.

  rewrite /enabled.

  move/enabledP: (inputEnabled P1 s.1 x H0); elim.
  simpl; rewrite /prePIOA_comptrans; intros.
  rewrite H2.
  caseOn (x \in cover (action P2)); intro.
  rewrite/action /cover !bigcup_fsetU in H3.
  move/fsetUP: H3; elim; intros.
  move/fsetUP: H3; elim; intros.
  move/cupP: H3; elim; intros.
  rewrite in_fset in H3.
  move/and3P: H3; elim => H3 _ H4.
  rewrite (eqP H3) in H4.
  move/enabledP: (inputEnabled P2 s.2 x H4).
  elim; intros.
  rewrite H5; done.
  move/cupP: H3; elim; intros.
  move/and3P: H3; elim; intros.
  have Hni := (notincover x _ H1 x1).
  rewrite H5 in Hni.
  rewrite in_fsetU H3 orbT //= in Hni.
  have: false.
  apply Hni; done.
  done.

  destruct H.
  have: false.
  move/cupP: H3; elim => x1; move/and3P; elim; intros.
  move/fdisjointP: (H5 _ _ H3 (pI_in_action P1)); intros.
  move: (H8 _ H7) => Hc.
  rewrite H0 in Hc; done.
  done.

  rewrite H3; destruct (tr P2 s.2 x); done.

  simpl; rewrite /enabled //= /prePIOA_comptrans.
  move/enabledP: (inputEnabled P2 s.2 x H0); elim; intros.
  rewrite H2.
  caseOn (x \in cover (action P1)).
  rewrite /cover /action !bigcup_fsetU.
  move/fsetUP; elim.
  move/fsetUP; elim.
  move/cupP; elim; intro; move/and3P; elim; intros.
  rewrite in_fset in H3.
  rewrite (eqP H3) in H5.
  move/enabledP: (inputEnabled P1 s.1 x H5).
  elim; intros mu Hmu; rewrite Hmu.
  done.
  move/cupP.
  elim; intro; move/and3P; elim; intros.
  have Hc := (notincover x _ H1 x1).
  rewrite in_fsetU in Hc; rewrite H3 orTb H5 in Hc.
  have: false.
  apply Hc; done.
  done.
  
  intro.
  destruct H.
  move/cupP: H3; elim => x1; move/and3P; elim; intros.
  move/fdisjointP: (H4 _ _ H3 (pI_in_action P2)).
  intros.
  rewrite (negbTE (H8 _ H7)) in H0; done.
  intro Hc; rewrite Hc.
  destruct (tr P1 s.1 x); done.

  }

  instantiate (1 := pTH P1 `|` pTH P2).
  instantiate (1 := pTO P1 `|` pTO P2).

  destruct H.
  constructor.

  move=> x Hx.

  intros; apply/fdisjointP; intros.
  rewrite in_fsetD in H2; move/andP: H2; elim; intros.
  move: H3; apply contraLR; rewrite !negbK.
  intro; apply/cupP; exists x; apply/and3P; done.
  intros.
  apply disjoint_setD.

  apply/fdisjointP; intros.
  move/fsetUP: H3; elim.
  move/fsetUP: H2; elim; intros.
  destruct (actionDisjoint P1).
  move/fdisjointP: (H5 _ H2).
  intro He; apply He; done.
  move: (H1 _ _ H2 (pI_in_action P1)); rewrite disjoint_sym; move/fdisjointP.
  intro Hd; apply Hd; done.

  move/fsetUP: H2; elim; intros.
  move: (H0 _ _ H2 (pI_in_action P2)); rewrite disjoint_sym; move/fdisjointP.
  intro Hd; apply Hd; done.

  destruct (actionDisjoint P2).
  move/fdisjointP: (H5 _ H2); intro Hd; apply Hd; done.

  move=> x y; move/fsetUP; elim; intro; move/fsetUP; elim; intro.

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

  move=> x y; move/fsetUP; elim; intro; move/fsetUP; elim; intros.
  destruct (actionDisjoint P1).
  apply H8; done.
  apply H; done.
  rewrite disjoint_sym; apply H; done.
  destruct (actionDisjoint P2); apply H8; done.

  move=> x y; move/fsetUP; elim; intro; move/fsetUP; elim; intros.
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
  intros; rewrite /actionDeterm.
  intros.
  apply/andP.
  intro.
  destruct H4.
  move/fsetUP: H0; elim; move/fsetUP; elim.


  move/enabledP: H4; elim; intros.
  move/enabledP: H5; elim; intros.
  rewrite //= in H0; rewrite /comp_prePIOA /prePIOA_comptrans in H0.
  rewrite //= in H5; rewrite /comp_prePIOA /prePIOA_comptrans in H5.
  have tin : T \in pTO P1 `|` pTH P1.
  apply/fsetUP; left;done.

  have Hc:= pActionDeterm P1 T tin s.1 x y H1 H2 H3.

  have: x \in cover (action P1).
  apply/cupP; exists T; rewrite /action.
  apply/and3P; split.
  apply/fsetUP; left; apply/fsetUP; right; done.
  done.
  done.
  intro xincov.

  have: y \in cover (action P1).
  apply/cupP; exists T; rewrite /action. apply/and3P; split. apply/fsetUP; left; apply/fsetUP; right; done.
  done.
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
  have tin : T \in pTO P2 `|` pTH P2.
  apply/fsetUP; left; done.

  have Hc:= pActionDeterm P2 T tin s.2 x y H1 H2 H3.

  have: x \in cover (action P2).
  apply/cupP; exists T; rewrite /action. apply/and3P; split. apply/fsetUP; left; apply/fsetUP; right; done.
  done.
  done.
  intro xincov.

  have: y \in cover (action P2).
  apply/cupP; exists T; rewrite /action. apply/and3P; split. apply/fsetUP; left; apply/fsetUP; right; done.
  done.
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
  have tin : T \in pTO P1 `|` pTH P1.
  apply/fsetUP; right;done.

  have Hc:= pActionDeterm P1 T tin s.1 x y H1 H2 H3.

  have: x \in cover (action P1).
  apply/cupP; exists T; rewrite /action. apply/and3P; split. apply/fsetUP; right. done.
  done.
  done.
  intro xincov.

  have: y \in cover (action P1).
  apply/cupP; exists T; rewrite /action. apply/and3P; split. apply/fsetUP; right; done.
  done.
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
  have tin : T \in pTO P2 `|` pTH P2.
  apply/fsetUP; right;done.

  have Hc:= pActionDeterm P2 T tin s.2 x y H1 H2 H3.

  have: x \in cover (action P2).
  apply/cupP; exists T; rewrite /action. apply/and3P; split. apply/fsetUP; right. done.
  done.
  done.
  intro xincov.

  have: y \in cover (action P2).
  apply/cupP; exists T; rewrite /action. apply/and3P; split. apply/fsetUP; right; done.
  done.
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
  move/fsetUP: (actSetValid P1 s.1 x x0); elim. move/fsetUP; elim.
  remember (x \in cover (pTO P2)); symmetry in Heqb; destruct b.
  intro; apply/fsetUP; left; apply/fsetUP; right.
  rewrite /cover.
  rewrite bigcup_fsetU.
  apply/fsetUP; right.
  apply Heqb.
  intro; apply/fsetUP; left; apply/fsetUP; left.
  rewrite in_fsetD; apply/andP; split.
  apply/fsetUP; left; done.
  rewrite coverU.
  rewrite notfsetU.
  apply/andP; split.
  destruct (actionDisjoint P1).
  apply/contraT; rewrite negbK; intro.
  move/cupP: H7; elim => z; move/and3P; elim; intros.
  move: (H2 _ H7).
  move/fdisjointP.
  move/(_ _ H1).
  rewrite H9; done.
  rewrite Heqb; done.

  intro; apply/fsetUP; left; apply/fsetUP; right.
  rewrite /cover bigcup_fsetU; apply/fsetUP; left; done.
  intro; apply/fsetUP; right.
  rewrite /cover bigcup_fsetU; apply/fsetUP; left; done.
  have: enabled P2 s.2 x.
  rewrite /enabled; destruct (tr P2 s.2 x); done.
  intro.

  move/fsetUP: (actSetValid P2 s.2 x x0); elim. move/fsetUP; elim.
  remember (x \in cover (pTO P1)); symmetry in Heqb; destruct b.
  intro; apply/fsetUP; left; apply/fsetUP; right.
  rewrite /cover.
  rewrite bigcup_fsetU.
  apply/fsetUP; left.
  apply Heqb.
  intro; apply/fsetUP; left; apply/fsetUP; left.
  rewrite in_fsetD; apply/andP; split.
  apply/fsetUP; right; done.
  rewrite /cover bigcup_fsetU notfsetU.
  rewrite Heqb.
  simpl.
  apply/cupP; elim => z.
  move/and3P; elim; intros.
  destruct (actionDisjoint P2).
  move: (H5 _ H2).
  move/fdisjointP.
  move/(_ _ H1).
  rewrite H4; done.

  intro; apply/fsetUP; left; apply/fsetUP; right.
  rewrite /cover bigcup_fsetU; apply/fsetUP; right; done.
  intro; apply/fsetUP; right.
  rewrite /cover bigcup_fsetU; apply/fsetUP; right; done.
Defined.

