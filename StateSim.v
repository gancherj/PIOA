

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat.


Section StateInj.
  
  Context {A : choiceType}.
  Context (P1 P2 : @PIOA A).
  Context (hc1 : closed P1).
  Context (hc2 : closed P2).

  Record StateInj (R : pQ P1 -> pQ P2) :=
    {
      siStart : R (start _) = (start _);
      siStep : forall T mu eta, T \in channels P1 -> isSubdist mu ->
          measMap mu (fun p => (R p.1, p.2)) = eta ->
          exists ts, all (fun x => x \in channels P2) ts /\
           measMap (appChan P1 T mu) (fun p => (R p.1, p.2)) =
                      runPIOA P2 ts eta 
      }.


  Lemma stateSimSound R : StateInj R -> @refinement _ P1 P2 hc1 hc2.
    case => h1 h2.
    move => ts Hts.

    have: exists ts', all (fun x => x \in channels P2) ts' /\
        measMap (runPIOA P1 ts (startTr P1)) (fun p => (R p.1, p.2)) = runPIOA P2 ts' (startTr P2).
    induction ts using last_ind.
    exists nil.
    split.
    done.

    rewrite //= /startTr //= measMap_ret; congr (ret _); rewrite //= h1 //=.

    rewrite all_rcons in Hts; move/andP: Hts => [Hx Hts].


    destruct (IHts Hts) as [ts' Hts'].

    have Hsd : isSubdist (runPIOA P1 ts (startTr P1)).
    apply runPIOA_subDist; rewrite //=.
    rewrite /startTr isSubdist_ret //=.
    destruct Hts' as [Hts'1 Hts'2].
    destruct (h2 _ _ _ Hx Hsd Hts'2) as [x0 Hx0].
    simpl in *.

    exists (ts' ++ x0).
    split.
    rewrite all_cat.
    destruct Hx0 as [Hx01 Hx02].
    rewrite Hx01 Hts'1 //=.
    rewrite runPIOA_app runPIOA_rcons //=.
    destruct Hx0; rewrite //=.

    elim => ts' Hts'.
    exists ts'.
    destruct Hts'; split; rewrite //=.
    rewrite -H0.
    rewrite /traceOf measMap_measMap //=.
 Qed.
End StateInj.

