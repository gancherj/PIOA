
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems.
Require Import fset.

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
      drelStep : forall mu eta T, T \in Tasks P1 -> R mu eta -> exists ts, all (isTask P2) ts /\ R (appTask P1 T mu) (runPIOA P2 ts eta)
                                                           }.

  Lemma DCSimP R : DCSim R -> @refinement _ P1 P2 HC1 HC2 0.
    case.
    intros.
    intros ts Hts.
    have: exists ts', all (isTask P2) ts' /\
        R (runPIOA _ ts (startTr P1)) (runPIOA _ ts' (startTr P2)).
    induction ts using last_ind.
    
    exists nil.
    done.
    rewrite all_rcons in Hts; move/andP: Hts => [h1 h2].
    destruct (IHts h2); clear IHts.
    destruct H.
    destruct (drelStep0 (runPIOA P1 ts (startTr P1)) (runPIOA P2 x0 (startTr P2)) x h1 H0).
    destruct H1.
    exists (x0 ++ x1).
    split.
    rewrite all_cat.
    rewrite H H1; done.
    rewrite runPIOA_app runPIOA_rcons.
    done.
    elim; intros.
    exists x.
    destruct H; split.
    done.
    apply drelObs0.
    done.
  Qed.

End DirectSim.

