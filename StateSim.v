

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
            meas_fmap (appTask T mu) (fun p => (R p.1, p.2)) ~~
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



