
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems.

Definition inputEquiv {A} (P1 P2 : @PIOA A) := pI P1 = pI P2.


Record coupling {A B : eqType} (D : Meas A) (R : A -> B -> bool) (D' : Meas B) C :=
  {
    _ : D ~~ meas_fmap C fst @ 0;
    _ : D' ~~ meas_fmap C snd @ 0;
    _ : forall p, p \in measSupport C -> R p.1 p.2
                                           }.

Section DirectSim.
  Context {A : finType}.
  Context (P1 P2 : @PIOA A).
  Context (HC1 : inputClosed P1).
  Context (HC2 : inputClosed P2).

  Record DCSim (R : Meas (Trace P1) -> Meas (Trace P2) -> Prop) :=
    {
      drelStart : R (startTr P1) (startTr P2);
      drelObs :
        forall mu eta, R mu eta -> meas_fmap mu snd ~~ meas_fmap eta snd @ 0;
      drelStep : forall mu eta T, R mu eta -> exists ts, R (appTask P1 T mu) (runPIOA P2 ts eta)
                                                           }.

  Lemma DCSimP R : DCSim R -> @refinement _ P1 P2 HC1 HC2 0.
    case.
    intros.
    intros ts.
    have: exists ts',
        R (runPIOA _ ts (startTr P1)) (runPIOA _ ts' (startTr P2)).
    induction ts using last_ind.
    exists nil.
    done.
    destruct IHts.

    destruct (drelStep0 _ _ x H).
    exists (x0 ++ x1).
    rewrite runPIOA_app.
    rewrite runPIOA_rcons.
    done.
    elim; intros.
    exists x.
    apply drelObs0; done.
  Qed.
End DirectSim.

  Definition traceProj1 {Act : finType} (P1 P2 : @PIOA Act) H : Trace (compPIOA P1 P2 H) -> Trace P1.
    elim.
    intros.
    constructor.
    apply (fst a).
    apply (filter (fun x => x \in cover (action P1)) b).
  Defined.

  Definition traceProj2 {Act : finType} (P1 P2 : @PIOA Act) H : Trace (compPIOA P1 P2 H) -> Trace P2.
    elim.
    intros.
    constructor.
    apply (snd a).
    apply (filter (fun x => x \in cover (action P2)) b).
  Defined.

Section DirectOpenSim.
  Context {A : finType}.
  Context (P1 P2 : @PIOA A).
  Context (Hequiv : inputEquiv P1 P2).

  Record DOSim (R : Meas (Trace P1) -> Meas (Trace P2) -> Prop) :=
    {
      dcrelStart : R (startTr P1) (startTr P2);
      dcrelObs :
        forall mu eta, R mu eta -> meas_fmap mu snd ~~ meas_fmap eta snd @ 0;
      dcrelStep : forall mu eta T, R mu eta -> exists ts, R (appTask P1 T mu) (runPIOA P2 ts eta);
      dcrelInput : forall mu eta i,
          R mu eta -> exists C, coupling mu (fun x y => enabled P1 x.1 i == enabled P2 y.1 i) eta C
                                         }.

                                    
  Context (Adv : @PIOA A).
  Context (HC1 : Compatible P1 Adv).
  Context (HC2 : Compatible P2 Adv).
  Context (IC1 : inputClosed (compPIOA P1 Adv HC1)).
  Context (IC2 : inputClosed (compPIOA P2 Adv HC2)).


  Lemma DOSimP R : DOSim R -> exists R', DCSim (compPIOA P1 Adv HC1) (compPIOA P2 Adv HC2) R'.
    intro.
    exists (fun mu eta => 
              
    refine (fun mu eta =>
              


                               
       


                                          
                   }.
  