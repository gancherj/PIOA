
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting Aux FastEnum Action PIOA.

Section Hiding.
  Context {G D : ctx} (P : PIOA G D) (o : seq (cdom G)) (Ho : all (fun x => x \in (outputs P)) o).

  Definition hide_tr : St P -> action (D :+: (G |c_ o)) + action G -> option {meas (St P)} :=
    fun s a =>
      match a with
        | inl (existT (inl h) m) => tr P s (inl (mkact D h m))
        | inl (existT (inr h) m) => tr P s (inr (mkact G (ssval h) m))
        | inr (existT c m) => tr P s (inr (mkact G c m))
                 end.

  Definition hide_tr_data : PIOA_data G (D :+: (G |c_ o)).
    econstructor.
    apply (start P).
    apply (inputs P).
    apply (seqD (outputs P) o).
    apply hide_tr.
  Defined.

  Lemma hidePIOA_spec : PIOA_spec hide_tr_data.
    unfold hide_tr_data; 
  constructor; simpl in *.

    apply/seq_disjointP => x Hx.
    rewrite mem_seqD negb_and.
    move/seq_disjointP: (disj_io (PIOAP P)).
    move/(_ _ Hx) => ->; done.

    rewrite //=.
    destruct h.
    apply (ad_h (PIOAP P)).
    intros.
    eapply ad_v.
    apply (PIOAP P).
    destruct s0; simpl in *.
    move/allP: Ho.
    move/(_ _ ssvalP).
    done.
    apply H.
    done.

    intros;
    apply (ad_v (PIOAP P) s).
    rewrite mem_seqD in H; elim (andP H); done.
    done.
    done.

    intros; apply (i_a (PIOAP P)).
    done.
 Qed.

 Definition hidePIOA : PIOA G (D :+: (G |c_ o)).
   apply (mkPIOA G _ hide_tr_data hidePIOA_spec).
 Defined.
End Hiding.

Section HidingAct.
  Context {G D : ctx} (P : PIOA G D) (o : seq (cdom G)) (Ho : all (fun x => x \in (outputs P)) o).


  Eval simpl in (H (hidePIOA P o Ho)).

  
  Lemma app_h_hidden (c : seq_sub o) x :
    app_h (hidePIOA P o Ho) (inr c) x =
    app_v P (ssval c) x <$> fst.
    rewrite /app_h /app_v.
    rewrite /pick_h.
    rewrite /pick_v.
    case: pickP; simpl; intros.
    remember (tr P x (inr (mkact G (ssval c) x0))) as t; rewrite -Heqt; destruct t.
    rewrite -(bind_ret m) !mbindA.
    apply mbind_eqP => y Hy.
    rewrite !ret_bind //=.
    rewrite !ret_bind //=.
    rewrite !ret_bind //=.
  Qed.
  
  Lemma act_hide_hv ( c : seq_sub o) mu : 
    act (hidePIOA P o Ho) (inl (inr c)) mu =
    (xt <- mu; p <- app_v P (ssval c) xt.1; ret (p.1, xt.2)).
    simpl.

    apply mbind_eqP => xt Hxt.
    rewrite app_h_hidden.
    rewrite mbindA.
    apply mbind_eqP => p Hp.
    rewrite !ret_bind //=.
  Qed.

  Lemma act_hide_h ( h : cdom D) mu :
    act (hidePIOA P o Ho) (inl (inl h)) mu =
    act P (inl h) mu.
    simpl.
    apply mbind_eqP => xt Hxt.
    rewrite /app_h /pick_h.
    case: pickP; simpl; done.
  Qed.

  Lemma act_hide_v (c : cdom G) mu :
    act (hidePIOA P o Ho) (inr c) mu =
    act P (inr c) mu.
    simpl.
    apply mbind_eqP => xt Hxt.
    rewrite /app_v /pick_v; case: pickP; simpl; done.
  Qed.
End HidingAct.
  
(* change context *)
Section ChangeH.
  Context {G D D' : ctx} (P : PIOA G D) (B : D' ~~ D).

  Definition changeHTr (s : St P) (a : action D' + action G) :=
    match a with
      | inl h => tr P s (inl (B *a h))
      | inr a => tr P s (inr a)
                     end.

  Definition changeH_data : PIOA_data G D'.
  econstructor.
  apply (start P).
  apply (inputs P).
  apply (outputs P).
  apply changeHTr.
  Defined.

  Definition changeH_spec : PIOA_spec changeH_data.
  constructor.
  apply (disj_io (PIOAP P)).

  simpl => s h m1 m2.
  rewrite !bijactionE => h1 h2.
  apply/eqP; eapply bijmsg_inj.
  apply/eqP.
  eapply (ad_h (PIOAP P) s).
  apply h1.
  done.

  simpl; apply (ad_v (PIOAP P)).
  apply (i_a (PIOAP P)).
  Qed.

  Definition changeH : PIOA G D'.
    apply (mkPIOA _ _ changeH_data changeH_spec).
  Defined.
End ChangeH.

Section ChangeHAct.
  Context {G D D' : ctx} (P : PIOA G D) (B : D' ~~ D).


  Lemma pick_h_changeh h s :
    pick_h (changeH P B) h s <$>o (fun a => B *a a) =
    pick_h P  (B *c h) s.
    move: h.
    rewrite /H //= => h.
    rewrite /pick_h.

    have <- : [pick m | enabled (changeH P B) s (inl (mkact D' h m)) ] <$>o (bij_msg B) =
          ([pick m | enabled P s (inl (mkact D (B *c h) m)) ]).
    case: pickP; simpl; intros; case: pickP; simpl; intros.
    rewrite /enabled //= in i, i0.
    rewrite bijactionE in i.
    congr (Some _).
    apply/eqP; apply (ad_h (PIOAP P) s); done.

    rewrite /enabled //= ?bijactionE in i, e.
    move: (e (B *m x)).
    rewrite i; done.

    rewrite /enabled //= in i, e.
    destruct (msg_inv B h x).
    rewrite H in i.
    move: (e x0).
    rewrite i //=.
    done.

    case: pickP; simpl; done.
  Qed.

  
  Lemma act_changeh_h (h : cdom D') mu :
    act (changeH P B) (inl h) mu =
    act P (inl (B *c h)) mu.
    simpl.
    apply mbind_eqP => xt Hxt.
    rewrite /app_h //=.
    rewrite -pick_h_changeh //=.
    rewrite /pick_h.
    case: pickP; simpl; intros; done.
  Qed.

  Lemma act_changeh_v (v : cdom G) mu :
    act (changeH P B) (inr v) mu =
    act P (inr v) mu.
    by done.
  Qed.
End ChangeHAct.