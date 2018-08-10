

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems DirectSim.


Section StateInj.
  
  Context {A : finType}.
  Context (P1 P2 : @PIOA A).
  Context (HC1 : inputClosed P1).
  Context (HC2 : inputClosed P2).

  Record StateInj (R : pQ P1 -> pQ P2) :=
    {
      siStart : R (start _) = (start _);
      siStep : forall T mu eta,
          meas_fmap mu (fun p => (R p.1, p.2)) ~~ eta @ 0 ->
          exists ts,
            meas_fmap (appTask _ T mu) (fun p => (R p.1, p.2)) ~~
                      runPIOA _ ts eta @ 0
      }.

  Definition stateInjToDC (R : pQ P1 -> pQ P2) : Meas [eqType of Trace P1] -> Meas [eqType of Trace P2] -> Prop :=
    fun mu eta => 
      meas_fmap mu (fun p => (R p.1, p.2)) ~~ eta @ 0.

  Lemma stateSimSound R : StateInj R -> @refinement _ P1 P2 HC1 HC2 0.
    intros.
    destruct H.
    intro.
    have: exists ts',
        meas_fmap (runPIOA P1 ts (startTr P1)) (fun p => (R p.1, p.2)) ~~ runPIOA P2 ts' (startTr P2) @ 0.
    induction ts using last_ind.
    exists nil.
    rewrite /meas_fmap //=.
    rewrite /startTr; dsimp.
    rewrite siStart0; reflexivity.
    destruct IHts.
    destruct (siStep0 x _ _ H).
    exists (x0 ++ x1).
    rewrite runPIOA_app.
    rewrite runPIOA_rcons //=.
    elim; intros.
    exists x.
    symmetry; rewrite /traceOf /meas_fmap.
    symmetry in H; rewrite (measBind_cong_l H).
    rewrite /meas_fmap.
    dsimp.
    apply measBind_cong_r; intros.
    dsimp; reflexivity.
    apply runPIOA_subDist.
    rewrite /startTr; dsubdist.
    intros; dsubdist.
  Qed.
End StateInj.


Definition taskProj {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (s : list (Task (compPIOA P1 P2 H))) : list (Task P1) * list (Task P2).
  induction s.
  exact (nil, nil).
  destruct a.
  simpl in i.
  caseOn (x \in pTO P1 :|: pTH P1).
  intro; have: Task P1. 
  econstructor.
  apply H0.
  intro tn.
  exact (tn :: IHs.1, IHs.2).
  caseOn (x \in pTO P2 :|: pTH P2).
  intros; have: Task P2.
  econstructor; apply H0.
  intro tn; exact (IHs.1, tn :: IHs.2).
  move/setUP.
  move/orP.
  rewrite negb_or.
  move/andP; elim.
  intros Hc1 Hc2.
  move/setUP; move/orP; rewrite negb_or; move/andP; elim.
  intros.
  move/setUP: i.
  move/
  rewrite Hc1 Hc2 H0 H1 in i.

  move/
  SearchAbout (_ \notin _ :|: _).
  
  move/setUP: i.
  move/orP.

  case.
  split.
  move/orP; elim.

Section StateInj_comp.
  Context {A : finType}.
  Context (P1 P2 Adv : @PIOA A).
  Context (Hc1 : Compatible P1 Adv).
  Context (Hc2 : Compatible P2 Adv).
  Definition p1a := compPIOA P1 Adv Hc1.
  Definition p2a := compPIOA P2 Adv Hc2.

  Lemma stateInj_comp (R : pQ P1 -> pQ P2) : StateInj P1 P2 R -> StateInj p1a p2a (fun p => (R p.1, p.2)).
    intros.
    destruct H; constructor.
    simpl.
    rewrite siStart0; done.
    intros.
    
  