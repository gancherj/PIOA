

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum Refinement Action Lifting CompPIOA.

Lemma is_chan_comp {G D D' : ctx} (P : PIOA G D) (E : PIOA G D') (he : env P E) x :
  is_chan (P ||| E) (inr x) = (x \in outputs P) || (x \in outputs E).
  rewrite /is_chan //=.
  rewrite mem_cat .
  elim (andP he) => _ ; rewrite /closed; move => /eqP //= ->.
  rewrite in_nil orFb mem_cat //=.
Qed.

Lemma is_chan_compare {G D : ctx} (P P' : PIOA G D) (hc : comparable P P') :
    is_chan P =1 is_chan P'.
    case; simpl.
    done.
    elim (andP hc).
    move/seq_eqmemP => hc1; move/seq_eqmemP => hc2 b; rewrite !mem_cat.
    rewrite !hc1 !hc2 //=.
Qed.

Lemma comparable_comp_r {G D D' : ctx} (P P' : PIOA G D) (E : PIOA G D') (hc : comparable P P') : comparable (P ||| E) (P' ||| E).
  elim (andP hc); move/seq_eqmemP => h1; move/seq_eqmemP => h2.
  apply/andP; split.
  simpl.
  apply/seq_eqmemP => x.
  rewrite !mem_seqD !mem_cat !h1 !h2 //=.
  apply/seq_eqmemP => x; rewrite !mem_cat !h2 //=.
Qed.

Lemma comparable_sym {G D : ctx} (P P' : PIOA G D) :
  comparable P P' = comparable P' P.
  apply Bool.eq_true_iff_eq; split; rewrite /comparable; move/andP; elim; move/seq_eqmemP => h1; move/seq_eqmemP => h2; apply/andP; split; apply/seq_eqmemP => x; rewrite ?h1 ?h2 //=.
Qed.


Lemma comparable_compatible_l {G D D' D'' : ctx} (P : PIOA G D) (P' : PIOA G D') (E : PIOA G D'') :
  comparable P P' -> compatible P E -> compatible P' E.
  move/andP; elim; move/seq_eqmemP => h1; move/seq_eqmemP => h2; rewrite /compatible.
  move/seq_disjointP => H; apply/seq_disjointP => x.
  rewrite -h2 //=; apply H.
Qed.

Section SimpleStateInj.
  
  Context {G D : ctx}.
  Context (P1 P2 : PIOA G D).
  Context (hcomp : comparable P1 P2).

  Check app_v.
  Check app_i.

  Record SimpleStateInj (R : St P1 -> St P2) :=
    {
      ssStart : R (start P1) = (start P2);
      ss_v : forall x c,
          c \in outputs P1 ->
          app_v P1 c x <$> (fun p => (R p.1, p.2)) = app_v P2 c (R x);
      ss_h : forall x h,
          app_h P1 h x <$> R = app_h P2 h (R x);
      ss_inp : forall x i,
          tag i \in inputs P1 ->
          app_i P1 i x <$> R = app_i P2 i (R x);
      }.

  Theorem stateSimSound R : SimpleStateInj R -> refines P1 P2 hcomp.
    case => h1 h2 h3 h4.
    move => D' E HE g Hg.
    exists g; split.
    rewrite /protocol_for.
    erewrite eq_all.
    rewrite /protocol_for in Hg;
    apply Hg.
    apply is_chan_compare.
    apply comparable_comp_r.
    rewrite comparable_sym //=.
    have: (run (P1 ||| E) g <$> fun p => ((R p.1.1, p.1.2), p.2)) = run (P2 ||| E) g.

    induction g using last_ind.
    rewrite /run //= /initDist //= !measE //= h1 //=.
    rewrite /protocol_for all_rcons in Hg. 
    move: Hg.

    case x => [h | v]; move => Hg.
    
    rewrite !run_rcons.
    rewrite -IHg.
    rewrite !mbindA //= !mbindA.
    apply mbind_eqP => y Hy; rewrite !measE.
    case h => [hl | hr]; rewrite //=.
    rewrite !app_h_comp_l !measE //=.
    rewrite -h3 !measE //=.
    apply mbind_eqP => z Hz; rewrite !measE //=.
    rewrite !app_h_comp_r; rewrite //= !measE //=.
    munder (rewrite measE); done.
    done.
    done.
    rewrite is_chan_comp in Hg; last by done.

    move/andP: Hg => [Hg1 Hg2].
    elim (orP Hg1) => Hv.
    remember (v \in inputs E) as ve; destruct ve; symmetry in Heqve.
    rewrite !run_rcons //= !measE.
    rewrite -IHg; last by done.
    rewrite !measE; apply mbind_eqP => y Hy; rewrite !measE.
    rewrite !app_v_comp_l_int.
    rewrite -h2.

    elim (app_vP P1 v y.1.1 Hv).
    move=> m mu Htr ->; rewrite //= !measE; munder (rewrite !measE; munder (rewrite !measE)); done. 
    done.
    move => H ->; rewrite !measE; done.
    done.
    eapply comparable_compatible_l.
    apply hcomp.
    elim (andP HE); done.
    elim (andP hcomp) => _ /seq_eqmemP => heq; rewrite -heq; done.
    done.
    elim (andP HE); done.
    done.
    done.

    rewrite !run_rcons //= !measE -IHg; last by done.
    rewrite !measE; apply mbind_eqP => y Hy; rewrite !measE.
    simpl.
    rewrite !(app_v_comp_l_ext).
    rewrite !measE //= -h2.
    rewrite !measE; munder (rewrite measE).
    done.
    done.
    eapply comparable_compatible_l.
    apply hcomp.
    elim (andP HE); done.
    elim (andP hcomp) => _ /seq_eqmemP => heq; rewrite -heq; done.
    by rewrite Heqve.
    by elim (andP HE).
    done.
    by rewrite Heqve.
    rewrite !run_rcons //= !measE -IHg; last by done.
    rewrite !measE; apply mbind_eqP => y Hy; rewrite !measE.

    remember (v \in inputs P1) as hv; destruct hv; symmetry in Heqhv.
    rewrite !app_v_comp_r_int //=.
    elim (app_vP E v y.1.2 Hv).
    move => m mu htr ->; rewrite !measE; munder (rewrite !measE; munder (rewrite !measE)).
    apply mbind_eqP => x0 Hx0.
    rewrite -h4.
    rewrite !measE //=; munder (rewrite !measE).
    done.
    done.
    move => _ ->; rewrite !measE //=.
    eapply comparable_compatible_l.
    apply hcomp.
    elim (andP HE); done.
    elim (andP hcomp) => /seq_eqmemP heq _; rewrite -heq; done. 
    by elim (andP HE).
    rewrite !app_v_comp_r_ext //=.
    elim (app_vP E v y.1.2 Hv).
    move => m mu htr ->; rewrite !measE. 
    munder (rewrite !measE).
    done.
    move => _ ->; rewrite !measE //=.
    eapply comparable_compatible_l.
    apply hcomp.
    elim (andP HE); done.
    elim (andP hcomp) => /seq_eqmemP heq _; rewrite -heq Heqhv //=.
    by elim (andP HE).
    rewrite Heqhv //=.

    move => <-.
    rewrite !measE.
    apply mbind_eqP => r Hr.
    rewrite !measE //=.
Qed.

End SimpleStateInj.