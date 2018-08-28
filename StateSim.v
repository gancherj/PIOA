

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems.
Require Import fset.


Section StateInj.
  
  Context {A : choiceType}.
  Context (P1 P2 : @PIOA A).
  Context (HC1 : inputClosed P1).
  Context (HC2 : inputClosed P2).

  Record StateInj (R : pQ P1 -> pQ P2) :=
    {
      siStart : R (start _) = (start _);
      siStep : forall T mu eta, T \in Tasks P1 -> isSubdist mu ->
          meas_fmap mu (fun p => (R p.1, p.2)) ~~ eta @ 0 ->
          exists ts, all (isTask P2) ts /\
            meas_fmap (appTask P1 T mu) (fun p => (R p.1, p.2)) ~~
                      runPIOA P2 ts eta @ 0
      }.


  Lemma stateSimSound R : StateInj R -> @refinement _ P1 P2 HC1 HC2 0.
    intros.
    destruct H.
    intro.
    intro.
    have: exists ts', all (isTask P2) ts' /\
        meas_fmap (runPIOA P1 ts (startTr P1)) (fun p => (R p.1, p.2)) ~~ runPIOA P2 ts' (startTr P2) @ 0.
    induction ts using last_ind.
    exists nil.
    split.
    done.

    rewrite /meas_fmap //=.
    rewrite /startTr; dsimp.
    rewrite siStart0; reflexivity.
    rewrite all_rcons in H; move/andP: H => [h1 h2].
    destruct (IHts h2); clear IHts.
    destruct H.
    have Hs: isSubdist (runPIOA P1 ts (startTr P1)).
    apply runPIOA_subDist.
    rewrite /startTr; dsubdist.
    destruct (siStep0 x _ _ h1 Hs H0).
    exists (x0 ++ x1).
    split.
    rewrite all_cat.
    destruct H1.
    rewrite H H1; done.

    rewrite runPIOA_app.
    rewrite runPIOA_rcons //=.
    destruct H1; done.

    elim; intros.
    exists x.
    split.
    destruct H0; done.
    destruct H0.
    symmetry; rewrite /traceOf /meas_fmap.
    symmetry in H1; rewrite (measBind_cong_l H1).
    rewrite /meas_fmap.
    dsimp.
    apply measBind_cong_r; intros.
    dsimp; reflexivity.
    apply runPIOA_subDist.
    rewrite /startTr; dsubdist.
    intros; dsubdist.
  Qed.
End StateInj.

