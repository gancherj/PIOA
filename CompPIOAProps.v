
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems StateSim.

  Definition tracePil {Act : finType} {P1 P2 : @PIOA Act} {H} : Trace (compPIOA P1 P2 H) -> Trace P1.
    elim.
    intros.
    constructor.
    apply (fst a).
    apply (filter (fun x => x \in cover (action P1)) b).
  Defined.

  Definition tracePir {Act : finType} {P1 P2 : @PIOA Act} {H} : Trace (compPIOA P1 P2 H) -> Trace P2.
    elim.
    intros.
    constructor.
    apply (snd a).
    apply (filter (fun x => x \in cover (action P2)) b).
  Defined.

  Definition traceInl {Act : finType} {P1 P2 : @PIOA Act} {H} : pQ P2 -> Trace P1 -> Trace (compPIOA P1 P2 H).
    intro; elim; intros; constructor.
    apply (a, X).
    apply b.
  Defined.

  Definition traceInr {Act : finType} {P1 P2 : @PIOA Act} {H} : pQ P1 -> Trace P2 -> Trace (compPIOA P1 P2 H).
    intro; elim; intros; constructor.
    apply (X ,a ).
    apply b.
  Defined.

Definition taskSplit {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (t : Task (compPIOA P1 P2 H)) :
  (Task P1) + (Task P2).
  destruct t.
  simpl in i.
  caseOn (tT \in pTO P1 :|: pTH P1).
  intro; left.
  econstructor.
  apply H0.
  caseOn (tT \in pTO P2 :|: pTH P2).
  intros; right; econstructor.
  apply H0.
  intros; exfalso.
  move/setUP: H0; move/orP; rewrite negb_or; move/andP; move => [h01 h02].
  move/setUP: H1; move/orP; rewrite negb_or; move/andP; move => [h11 h12].
  move/setUP: i; elim.
  move/setUP; elim.
  rewrite (negbTE h11); done.
  rewrite (negbTE h01); done.
  move/setUP; elim.
  rewrite (negbTE h12); done.
  rewrite (negbTE h02); done.
Defined.

Definition taskInjl {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (t : Task P1) :
  Task (compPIOA P1 P2 H).
  destruct t; econstructor.
  simpl.
  move/setUP: i; elim; intros.
  apply/setUP; left; apply/setUP; left; apply H0.
  apply/setUP; right; apply/setUP; left; apply H0.
Defined.

Definition taskInjr {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (t : Task P2) :
  Task (compPIOA P1 P2 H).
  destruct t; econstructor.
  simpl.
  move/setUP: i; elim; intros.
  apply/setUP; left; apply/setUP; right; apply H0.
  apply/setUP; right; apply/setUP; right; apply H0.
Defined.


Definition appTaskLeft {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (t : Task P1) mu := appTask (taskInjl _ P2 H t) mu.

Lemma meas_fmap_isSubdist {A B : eqType} (mu : Meas A) (f : A -> B) : isSubdist mu -> isSubdist (meas_fmap mu f).
  rewrite /isSubdist.
  rewrite /measMass.
  rewrite /meas_fmap.
  rewrite /measBind /measJoin /measSum.
  rewrite big_flatten !big_map.
  simpl.
  intros.
  have:  \big[padd/0]_(j <- mu) \big[padd/0]_(i <- [:: (j.1 * 1, f j.2)]) i.1 =
         \big[padd/0]_(j <- mu) j.1.
  apply eq_bigr; intros; rewrite big_cons big_nil.
  simpl.
  rewrite paddr0 pmulr1; done.
  intro He; rewrite He; done.
Qed.

Lemma compat_hidden_disabled {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (T : Task P1) x s:
  x \in T -> hiddenTask T -> ~~ enabled P2 s x.
  intros; apply/contraT; rewrite negbK; intros.

  have HC := actSetValid P2 s x H2.
  destruct H.
  move/setUP: HC; elim.
  move/setUP; elim; intros.

  move/disjointP: (H3 _ _ H1 (pI_in_action P2)).
  move/(_ _ H0).
  rewrite H5; done.

  move/bigcupP: H5; elim; intros.
  Check tO_in_action.
  move/disjointP: (H3 _ _ H1 (tO_in_action P2 _ H5)).
  move/(_ _ H0); rewrite H6; done.

  move/bigcupP; elim; intros.
  move/disjointP: (H3 _ _ H1 (tH_in_action P2 _ H5)).
  move/(_ _ H0).
  rewrite H6; done.
Qed.  


Lemma enabled_hiddenE {A} (P1 P2 : @PIOA A) H (T : Task P1) x s :
  x \in T -> hiddenTask T -> enabled P1 s.1 x =
                             enabled (compPIOA P1 P2 H) s x.
  intros.

  simpl.
  have: tr P2 s.2 x = None.
  remember (tr P2 s.2 x) as eta; destruct eta.
  exfalso; apply/negP. eapply compat_hidden_disabled.
  apply H.
  apply H0.
  done.
  instantiate (1 := s.2); rewrite /enabled -Heqeta //=.
  done.
  intros.
  rewrite /enabled //= /prePIOA_comptrans.
  rewrite x0.
  have: x \notin cover (action P2).
  destruct H.
  apply/contraT; rewrite negbK; intros.
  move/bigcupP: H4; elim; intros.
  move/disjointP: (H2 _ _ H1 H4).
  move/(_ _ H0).
  rewrite H5; done.
  intro.
  rewrite x1.
  destruct (tr P1 s.1 x); done.
Qed.

Section CompPIOA_symm.
  Context {A : finType}.
  Context (P1 P2 : @PIOA A).
  Context (Hc : Compatible P1 P2).
  Context (ic : inputClosed (compPIOA P1 P2 Hc)).

  Lemma ic2 : inputClosed (compPIOA P2 P1 (compatible_sym _ _ Hc)).
    rewrite /inputClosed.
    simpl.
    have ic2 := ic.
    rewrite /inputClosed in ic2.
    simpl in ic2.
    apply setP => x.
    rewrite in_set0.
    apply/setDP.
    elim.
    intros.
    apply setP in ic2.
    move/setDP: (ic2 x).
    rewrite in_set0 //=.
    elim.
    split.
    move/setUP: H.
    elim.

    intro; apply/setUP; right; done.
    intro; apply/setUP; left; done.
    move/bigcupP: H0; intros.
    apply/bigcupP.
    elim.
    intros.
    apply H0.
    exists x0.
    move/setUP: H1; elim.
    intro; apply/setUP; right; done.
    intro; apply/setUP; left; done.
    done.
  Qed.

  Lemma compPIOA_sym : @refinement _ (compPIOA P1 P2 Hc) (compPIOA P2 P1 (compatible_sym _ _ Hc)) ic ic2 0.
    eapply stateSimSound.
    instantiate (1 := (fun p => (p.2, p.1))).
    constructor.
    done.
    simpl.
    intros.
    destruct T.
    have: tT \in pTO (compPIOA P2 P1 (compatible_sym _ _ Hc)) :|: pTH (compPIOA P2 P1 (compatible_sym _ _ Hc)).
    admit.
    intro.
    Check Build_Task.
    exists ((Build_Task _ _ tT x) :: nil).
    simpl.
    rewrite /meas_fmap /appTask.
    dsimp.
    symmetry in H; symmetry; rewrite (measBind_cong_l H).
    rewrite /meas_fmap; dsimp.
    apply measBind_cong_r; intros.
    dsimp.
    rewrite /runTask.
    simpl.



        
(*
Lemma appTaskLeftHidden {A} (P1 P2 : @PIOA A) H t mu : isSubdist mu ->
  hiddenTask t -> appTask P1 t (meas_fmap mu traceProj1) ~~ meas_fmap (appTaskLeft _ P2 H t mu) traceProj1 @ 0. 
  intros.
  have: hiddenTask  (taskInjl _ P2 H t).
  rewrite /hiddenTask /taskInjl.
  destruct t.
  simpl.
  rewrite /hiddenTask //= in H1.
  apply/setUP; left; done.
  intro.
  rewrite /appTaskLeft /meas_fmap /appTask.
  dsimp.
  apply measBind_cong_r; intros.
  dsimp.
  destruct x0.
  simpl.

  destruct t.
  rewrite /taskInjl.
  simpl.
  have: [pick x1 in x0 | enabled P1 s.1 x1] = [pick x1 in x0 | enabled (comp_prePIOA P1 P2) s x1].
  case:pickP.
  case:pickP.
  intros.
  rewrite /enabled in i0.
  simpl in i0.
  destruct (hiddenP t (meas_fmap mu traceProj1) H1 (meas_fmap_isSubdist mu traceProj1 H0)).
  destruct (hiddenP (taskInjl P1 P2 H t) mu x H0).
  rewrite H2.
  rewrite /appTaskLeft /meas_fmap; symmetry; rewrite (measBind_cong_l H3).
  dsimp.
  apply measBind_cong_r; intros.
  dsimp.

  symmetry; rewrite (meas_fmap_conH3.
  
  rewrite /appTask
  
*)