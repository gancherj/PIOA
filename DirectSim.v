
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

  Record DCSim (R : Meas ([eqType of Trace P1]) -> Meas ([eqType of Trace P2]) -> Prop) :=
    {
      drelStart : R (startTr P1) (startTr P2);
      drelObs :
        forall mu eta, R mu eta -> meas_fmap mu snd ~~ meas_fmap eta snd @ 0;
      drelStep : forall mu eta T, R mu eta -> exists ts, R (appTask T mu) (runPIOA P2 ts eta)
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

