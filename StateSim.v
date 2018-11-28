

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum Refinement Action Lifting.


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
End SimpleStateInj.