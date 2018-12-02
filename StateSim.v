

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


  Lemma stateSimSound R : SimpleStateInj R -> simulation_sameh P1 P2 hcomp (fun mu eta => (mu <$> (fun p => (R p.1, p.2)) == eta)).
    case => h1 h2 h3.
    constructor.
    simpl => mu eta.
    move/eqP => <-.
    rewrite mbindA.
    apply mbind_eqP => x Hx.
    rewrite ret_bind //=.
    rewrite /initDist ret_bind h1 //=.
    move => mu eta hc Hlc.
    move/eqP => <-.

    apply id_lifting.
    destruct hc; simpl.
    apply/eqP; rewrite !mbindA; apply mbind_eqP => xt Hxt.
    rewrite ret_bind mbindA //=.
    rewrite -h3 mbindA //=.
    apply mbind_eqP => y Hy.
    rewrite !ret_bind //=.

    apply/eqP; rewrite !mbindA; apply mbind_eqP => xt Hxt.
    rewrite ret_bind mbindA //=.
    rewrite -h2 .
    rewrite mbindA; apply mbind_eqP => y Hy.
    rewrite !ret_bind //=.
    done.

    move => mu eta a Ha; move/eqP => <-.
    rewrite !mbindA; apply/eqP.
    apply mbind_eqP => x Hx.
    rewrite !mbindA ret_bind //=.
    rewrite -ss_inp0.
    rewrite mbindA.
    apply mbind_eqP => y Hy.
    rewrite !ret_bind //=.
    done.
Qed.

  Theorem ss2 R : SimpleStateInj R -> refines P1 P2 hcomp.
    case => h1 h2 h3 h4.
    move => D' E HE g Hg.
    exists g; split.
    rewrite /protocol_for.
    admit.
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
    admit.
    admit.
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
    admit.
    admit.
    by rewrite Heqve.
    by elim (andP HE).
    done.
    by rewrite Heqve.
    rewrite !run_rcons //= !measE -IHg; last by done.
    rewrite !measE; apply mbind_eqP => y Hy; rewrite !measE.
    admit.

    move => <-.
    rewrite !measE.
    apply mbind_eqP => r Hr.
    rewrite !measE //=.
Admitted.

End SimpleStateInj.