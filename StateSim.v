

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum Refinement Action Closure CompPIOA ParaSim.

Section StateSim.
  Context {G D : ctx}.
  Context (P1 P2 : PIOA G D).
  Context (hcomp : comparable P1 P2).
  Context (R : {meas St P1} -> {meas St P2} -> bool).

  Definition liftR (mu : {meas St P1 * trace P1}) (eta : {meas St P2 * trace P2}) :=
    all (fun x => (all (fun y => x.2 == y.2) (support mu))) (support eta) && (R (mu <$> fst) (eta <$> fst)).

  Lemma liftRP mu eta : mass mu != 0 -> mass eta != 0 ->
    reflect (exists S S' t, [/\ mu = S ** ret t, eta = S' ** ret t & R S S']) (liftR mu eta).
    move => hmu heta.
    apply/(iffP idP).
    move/andP; elim.
    move/constant_rP.
    move/(_ nil heta hmu).
    elim => S; elim => S'; elim => t; elim => heq1 heq2; subst => HR.
    exists S'; exists S; exists t; split.
    done.
    done.
    move: HR; msimp; done.
    elim => S; elim => S'; elim => t; elim => heq1 heq2 hr; subst.
    apply/andP; split.
    apply/allP => x.
    move/support_bindP; elim => a; elim => Ha.
    msimp; rewrite in_ret; move/eqP => ->.
    apply/allP => y.
    move/support_bindP; elim => b; elim => Hb.
    rewrite in_ret; move/eqP => ->.
    done.
    msimp; done.
  Qed.
    

  Record StateSim :=
    {
      ssStart : R (ret start P1) (ret start P2);
      ss_v : forall mu eta c t,
          c \in outputs P1 ->
          mass mu != 0 ->
          mass eta != 0 ->
          R mu eta ->
          closure liftR (act P1 (inr c) (mu ** ret t)) (act P2 (inr c) (eta ** ret t));
      ss_h : forall mu eta h t,
          R mu eta ->
          mass mu != 0 ->
          mass eta != 0 ->
          closure liftR (act P1 (inl h) (mu ** ret t)) (act P2 (inl h) (eta ** ret t));
      ss_inp : forall mu eta i t,
          R mu eta ->
          mass mu != 0 ->
          mass eta != 0 ->
          tag i \in inputs P1 ->
          closure liftR (x <- mu; s' <- app_i P1 i x; ret (s', i :: t))
                    (x <- eta; s' <- app_i P2 i x; ret (s', i :: t))
      }.

  Lemma stateSim_ShSim : StateSim -> ShSim P1 P2 liftR.
    case => h1 h2 h3 h4; constructor.
    move => mu eta [Hmu1 Hmu2] [Heta1 Heta2]; move/liftRP.
    rewrite (eqP Hmu2) (eqP Heta2); move/(_ is_true_true is_true_true).

    elim => S; elim => S'; elim => t; elim; intros; subst.
    exists S; exists S'; exists t; split; done.
    apply/liftRP.
    rewrite /initDist mass_ret //=.
    rewrite /initDist mass_ret //=.
    exists (ret start P1); exists (ret start P2); exists nil; split.
    rewrite /initDist !measE //=.
    rewrite /initDist !measE //=.
    done.

    move => c mu eta [Hmu1 Hmu2] [Heta1 Heta2]; move/liftRP.
    rewrite (eqP Hmu2) (eqP Heta2); move/(_ is_true_true is_true_true).
    elim => S; elim => S'; elim => t; elim; intros; subst.
    rewrite /isdist !mass_mprod !mass_ret !pmulr1 in Hmu2, Heta2.
    apply h2.
    done.
    rewrite (eqP Hmu2) //=.
    rewrite (eqP Heta2) //=.
    done.

    move => h mu eta [Hmu1 Hmu2] [Heta1 Heta2]; move/liftRP.
    rewrite (eqP Hmu2) (eqP Heta2); move/(_ is_true_true is_true_true).
    elim => S; elim => S'; elim => t; elim; intros; subst.
    rewrite /isdist !mass_mprod !mass_ret !pmulr1 in Hmu2, Heta2.
    apply h3.
    done.
    rewrite (eqP Hmu2) //=.
    rewrite (eqP Heta2) //=.

    move => a mu eta [Hmu1 Hmu2] [Heta1 Heta2]; move/liftRP.
    rewrite (eqP Hmu2) (eqP Heta2); move/(_ is_true_true is_true_true).
    elim => S; elim => S'; elim => t; elim; intros; subst.
    rewrite /isdist !mass_mprod !mass_ret !pmulr1 in Hmu2, Heta2.
    msimp.
    rewrite /act_i; msimp.
    apply h4.
    done.
    rewrite (eqP Hmu2) //=.
    rewrite (eqP Heta2) //=.
    done.
 Qed.


 Lemma stateSim_sound : StateSim -> refines P1 P2 hcomp.
   intros.
   eapply ShSim_refines.
   apply stateSim_ShSim.
   done.
 Qed.
End StateSim.
          

Section SimpleStateInj.
  
  Context {G D : ctx}.
  Context (P1 P2 : PIOA G D).
  Context (hcomp : comparable P1 P2).

  Record SimpleStateInj (R : St P1 -> St P2) :=
    {
      ssiStart : R (start P1) = (start P2);
      ssi_v : forall x c,
          c \in outputs P1 ->
          app_v P1 c x <$> (fun p => (R p.1, p.2)) = app_v P2 c (R x);
      ssi_h : forall x h,
          app_h P1 h x <$> R = app_h P2 h (R x);
      ssi_inp : forall x i,
          tag i \in inputs P1 ->
          app_i P1 i x <$> R = app_i P2 i (R x);
      }.

  Theorem ssi_statesim R : SimpleStateInj R -> StateSim P1 P2 (fun mu eta => eta == mu <$> R).
    case => h1 h2 h3 h4; constructor.
    rewrite -h1 !measE //=.
    intros.
    move/eqP: H2 => H2; subst.
    simpl.
    msimp.
    apply closure_bind => x Hx.
    rewrite -h2; rewrite //=.
    msimp.
    apply closure_bind => y Hy.
    apply id_closure.
    apply isdist_ret.
    apply isdist_ret.
    apply/andP; split.
        rewrite !support_ret //= eq_refl //=.
        msimp; done.


    move => mu eta h t /eqP -> Hmu Heta; msimp; apply closure_bind => x Hx.
    rewrite -h3; msimp; apply closure_bind => y Hy; apply id_closure.
    apply isdist_ret.
    apply isdist_ret.
    apply/andP; split.
    rewrite !support_ret //= eq_refl //=.
    msimp; done.

    move => mu eta i t /eqP -> Hc Hmu Heta; simpl; msimp. apply closure_bind => x Hx.
    rewrite -h4.
    msimp.
    apply closure_bind=> y Hy.
    apply id_closure.
    apply isdist_ret.
    apply isdist_ret.
    apply/andP; split.
    rewrite !support_ret //= eq_refl //=.
    msimp; done.
    done.
  Qed.


  Theorem ssi_refines R : SimpleStateInj R -> refines P1 P2 hcomp.
    intro; eapply stateSim_sound.
    apply ssi_statesim.
    apply H.
  Qed.
End SimpleStateInj.
