

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum Refinement Action Lifting.


Section SimpleStateInj.
  
  Context {G D : ctx}.
  Context (P1 P2 : PIOA G D).
  Context (hcomp : comparable P1 P2).

  Print simulation_sameh.

  Record SimpleStateInj (R : St P1 -> St P2) :=
    {
      ssStart : R (start P1) = (start P2);
      ss_lc : forall mu hc,
          locally_controlled P1 hc ->
          ((act P1 hc mu) <$> fun p => (R p.1, p.2)) = act P2 hc (mu <$> fun p => (R p.1, p.2));
      ss_inp : forall mu a,
          tag a \in inputs P1 ->
          ((apply_i P1 a mu) <$> fun p => (R p.1, p.2)) = apply_i P2 a (mu <$> fun p => (R p.1, p.2));}.


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
    rewrite h2 //=.
    intros; apply id_lifting.
    rewrite h3 //=.
    rewrite -(eqP H0) //=.
  Qed.
End SimpleStateInj.