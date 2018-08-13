

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems DirectSim CompPIOAProps.


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

Section ParaStateInj.
  Context {A : finType}.
  Context (P1 P2 Adv : @PIOA A).
  Context (Hc1 : Compatible P1 Adv).
  Context (Hc2 : Compatible P2 Adv).
  Context (Hine : pI P1 = pI P2).
  Check tr.

  Record ParaStateInj (R : pQ P1 -> pQ P2) :=
    {
      piInput : forall s x, x \in pI P1 ->
                                  match tr P1 s x, tr P2 (R s) x with
                                  | Some mu, Some eta => meas_fmap mu R ~~ eta @ 0
                                  | _, _ => false
                                           end;
      piStart : R (start _) = (start _);
      piStep : forall T mu eta,
          meas_fmap mu (fun p => (R p.1, p.2)) ~~ eta @ 0 ->
          exists ts,
            meas_fmap (appTask T mu) (fun p => (R p.1, p.2)) ~~
                      runPIOA _ ts eta @ 0
                      }.

  Context (ic1 : inputClosed (compPIOA P1 Adv Hc1)).
  Context (ic2 : inputClosed (compPIOA P2 Adv Hc2)).

  Lemma paraStateSound R : ParaStateInj R -> @refinement _ (compPIOA P1 Adv Hc1) (compPIOA P2 Adv Hc2) ic1 ic2 0.
    intros.
    eapply stateSimSound.
    instantiate (1 := fun p => (R p.1, p.2)).
    destruct H; constructor.
    simpl.
    rewrite piStart0; done.
    intros.
    destruct T.
    simpl in i.
    elim (setUP i).
    move/setUP; elim.
    intros.
    Check Build_Task.
    have: tT \in pTO P1 :|: pTH P1.
    apply/setUP; left; done.
    intro x.
    have: meas_fmap (meas_fmap mu (fun x => (x.1.1, x.2))) (fun p => (R p.1, p.2)) ~~
          meas_fmap eta (fun x => (x.1.1, x.2)) @ 0.
    admit.
    intro xeq.
    destruct (piStep0 (Build_Task _ _ _ x) (meas_fmap mu (fun x => (x.1.1, x.2))) (meas_fmap eta (fun x => (x.1.1, x.2))) xeq).
    exists (map (fun t => taskInjl _ _ _ t) x0).
    simpl in H1.
    simpl.
    admit.
    intros.
    have: tT \in pTO Adv :|: pTH Adv.
    apply/setUP; left; done.
    intro.
    exists (map (taskInjr _ _ _) (Build_Task _ _ _ x :: nil)).
    simpl.
    admit.


    (* hidden *)
    admit.
    Admitted.

          



