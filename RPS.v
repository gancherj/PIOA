
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Aux PIOA Ascii String CompPIOA SSRString FastEnum Action Refinement StateSim Compute PIOAOps.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import Lens.Lens Lens.TC.

Require Import Derive.

Set Primitive Projections.


Lemma ctx_is_empty_l_spec {C D : ctx} (H : C ~~ emptyCtx) :
  ctxbij_spec D (C :+: D) (fun x => inr x) (fun x => match x with | inl a => match (lr H a) with end | inr a => a end).
  constructor.
 done.
 case => a; rewrite //=.
 generalize (H *c a).
 case.
 move => x; simpl.
 done.
Qed.

Definition ctx_is_empty_l {C D : ctx} (H : C ~~ emptyCtx) : D ~~ (C :+: D).
  econstructor; apply (ctx_is_empty_l_spec H).
Defined.

Lemma ctx_is_empty_l_appc {C D : ctx} (H : C ~~ emptyCtx) c :
  (@ctx_is_empty_l C D H) *c c =
  inr c.
  done.
Qed.  

Inductive RPSContextM :=
  choose | committed | reveal | commit | open | winner.


Definition rps_context_enc (a : RPSContextM) :=
  match a with
  | choose => (None, false) 
  | committed => (None, true)
  | reveal => (Some false, false)
  | commit => (Some false, true) 
  | open => (Some true, false) 
  | winner => (Some true, true) end .

Definition rps_context_dec x :=
  match (x) with
    | (None, false) => choose
    | (None, true) => committed
    | (Some false, false) => reveal
    | (Some false, true) => commit
    | (Some true, false) => open
    | (Some true, true) => winner
  end.


Lemma rps_context_can : cancel rps_context_enc rps_context_dec.
  by case.
Qed.

Canonical rps_eq := EqType RPSContextM (CanEqMixin rps_context_can).
Canonical rps_choice := ChoiceType RPSContextM (CanChoiceMixin rps_context_can).
Canonical rps_count := CountType RPSContextM (CanCountMixin rps_context_can).
Canonical rps_fin := FinType RPSContextM (CanFinMixin rps_context_can).

Instance rps_fe : FastEnum [finType of RPSContextM] := { fastEnum := [:: choose; committed; reveal; commit; open; winner]}.
apply uniq_perm_eq; rewrite ?enum_uniq //= => x; case x; rewrite mem_enum //=.
Defined.

Inductive play := rock | paper | scissors.

Definition play_eq m1 m2 :=
  match m1,m2 with
    | rock,rock => true | paper,paper => true | scissors,scissors => true | _,_ => false end.

Definition play_obool m :=
  match m with
    | rock => None | paper => Some false | scissors => Some true end.

Definition obool_play m :=
  match m with
    | None => rock | Some false => paper | Some true => scissors end.

Lemma play_obool_can : cancel play_obool obool_play.
  by case.
Qed.

Canonical play_eqType := EqType play (CanEqMixin play_obool_can).
Canonical play_choiceType := ChoiceType play (CanChoiceMixin play_obool_can).
Canonical play_countType := CountType play (CanCountMixin play_obool_can).
Canonical play_finType := FinType play (CanFinMixin play_obool_can).

Instance play_fe : FastEnum [finType of play] := {fastEnum := [:: rock; paper; scissors]}.
  apply uniq_perm_eq; rewrite ?enum_uniq //= => x; case x; rewrite mem_enum //=.
Defined.

Definition rps_win_a (va vb : option play) :=
  match va, vb with
    | Some x, Some y => ((x == rock) && (y == scissors)) || ((x == paper) && (y == rock)) || ((x == scissors) && (y == paper))
    | _, _ => false
                end.

Definition rps_win_b (va vb : option play) :=
  match va, vb with
    | Some x, Some y => ((x == rock) && (y == paper)) || ((x == paper) && (y == scissors)) || ((x == scissors) && (y == rock))
    | _, _ => false
                end.

Definition rps_win_tie (va vb : option play) :=
  match va, vb with
  | Some x, Some y => x == y
  | _, _ => false
              end.

Lemma rpsP (va vb : play) : [|| rps_win_a (Some va) (Some vb), rps_win_b (Some va) (Some vb) | rps_win_tie (Some va) (Some vb)].
  destruct va; destruct vb; simpl; done.
Qed.

Definition RPSContext_f (x : RPSContextM * bool) : finType  :=
  match x.1 with
    | (choose) => [finType of play]
    | (committed) => [finType of unit]
    | (reveal) => [finType of play]
    | (commit) => [finType of play]
    | (open) => [finType of unit]
    | (winner) => [finType of option bool]
                            end.

Definition RPSContext :=
  mkCon ([finType of RPSContextM * bool])%type RPSContext_f.

Instance rpscontext_fe (x : cdom RPSContext) : FastEnum (RPSContext x).
case x; case; case; simpl; rewrite /RPSContext_f //=; apply _.
Defined.

Record playerSt :=
  PlayerSt {
      val1 : option play;
      val2 : option play;
      com1 : bool;
      com2 : bool }.

Run TemplateProgram (deriveFinRecord playerSt "f" "g" "playerSt_cancel1" "playerSt_cancel2").
Next Obligation.
  by case.
Defined.
Next Obligation.
  by case => x; case => y; case => z w.
Defined.

Run TemplateProgram (genLens playerSt).


Instance playerSt_fe : FastEnum [finType of playerSt] := fastEnum_bij playerSt_cancel2 playerSt_cancel1.

Definition player_trans (wh : bool) (s : playerSt) (a : action emptyCtx + action RPSContext) : option {meas playerSt}:=
  match a with
  | inr (existT (choose, b) msg) =>
        if (wh == b) then
        if (val1 s) == None then Some (ret (set _val1 (Some msg) s)) else Some (ret s)
        else None
  | inr (existT (commit, b) msg) =>
        if (wh == b) && (val1 s == Some msg) then
        Some (ret set _com1 true s)
        else None
  | inr (existT (committed, b) msg) =>
        if (wh != b) then
        Some (ret set _com2 true s)
        else None
  | inr (existT (open, b) msg) =>
        if (wh == b) && com1 s && com2 s then
        Some (ret s)
        else None
  | inr (existT (reveal, b) msg) =>
        if (wh != b) then
          if (val2 s == None) then
            Some (ret set _val2 (Some msg) s)
          else Some (ret s)
        else None
  | inr (existT (winner, b) msg) =>
    multiIf [::
        ([&& wh == b, msg == Some true & rps_win_a (val1 s) (val2 s)], (ret s)) ;
        ([&& wh == b, msg == Some false & rps_win_b (val1 s) (val2 s)], (ret s)) ;
        ([&& wh == b, msg == None & rps_win_tie (val1 s) (val2 s)], (ret s)) ]
  | _ => None                                                                                          
      end.

Definition player_data (wh : bool) : PIOA_data RPSContext emptyCtx.
econstructor.
apply (PlayerSt None None false false).
apply ([:: (choose, wh); (committed, ~~ wh); (reveal, ~~ wh)]).
apply ([:: (commit, wh); (open, wh); (winner, wh)]).
apply (player_trans wh).
Defined.

Lemma if_eq_irrel {A} (b : bool) (c e d : A) (p : Prop) :
  (c = d -> p) -> (e = d -> p) -> (if b then c else e) = d -> p.
  intros ; destruct b.
  apply H; done.
  apply H0; done.
Qed.




Lemma player_spec wh : PIOA_spec (player_data wh).
econstructor.
done.
done.
  intros; apply (decide_ad_vP RPSContext emptyCtx _ [finType of playerSt] (player_trans wh) [:: (commit, wh); (open, wh); (winner, wh)] s). 
  done.
  done.
  done.
  case wh; vm_compute; done.

  
  intros; apply (decide_i_aP RPSContext emptyCtx _ [finType of playerSt] _  [:: (choose, wh); (committed, ~~ wh); (reveal, ~~ wh)] ).
  done.
  case wh; vm_compute; done.
  move => s a mu; destruct a.
  done.

  destruct a; simpl.
  destruct x as [r b]; simpl; destruct r; pioa_dist_tac.
Qed.
  

Definition playerA := mkPIOA _ _ (player_data false) (player_spec false).
Definition playerB := mkPIOA _ _ (player_data true) (player_spec true).


Definition Ftrans (s : playerSt) (a : action emptyCtx + action RPSContext) : option {meas playerSt} :=
  match a with
  | inr (existT (commit, false) msg) =>
    Some (ret set _val1 (if view _val1 s == None then Some msg else view _val1 s) s)
  | inr (existT (commit, true) msg) =>
    Some (ret set _val2 (if view _val2 s == None then Some msg else view _val2 s) s)
  | inr (existT (committed, false) _) =>
    if (val1 s) != None then Some (ret s) else None
  | inr (existT (committed, true) _) =>
    if (val2 s) != None then Some (ret s) else None
  | inr (existT (open, false) _) =>
    Some (ret (set _com1 true s))
  | inr (existT (open, true) _) =>
    Some (ret (set _com2 true s))
  | inr (existT (reveal, false) x) =>
    if ((com1 s) && ((val1 s) == Some x)) then Some (ret s) else None
  | inr (existT (reveal, true) x) =>
    if ((com2 s) && ((val2 s) == Some x)) then Some (ret s) else None
  | _ => None end.

Definition funct_data : PIOA_data RPSContext emptyCtx.
econstructor.
apply (PlayerSt None None false false).
    apply [:: (commit, true); (commit, false); (open, true); (open,false)].
apply    [:: (committed, true); (committed, false); (reveal, true); (reveal, false)].
apply Ftrans.
Defined.

Lemma funct_spec : PIOA_spec funct_data.
econstructor.
done.
done.
  intros; eapply (decide_ad_vP RPSContext emptyCtx _ [finType of playerSt] _ _ s).
  apply H.
  apply H0.
  done.
  vm_compute; done.

  intros; eapply decide_i_aP.
  apply H.
  vm_compute; done.
  move => s a mu; destruct a.
  done.
  destruct a as [r b]; simpl; destruct r.
  destruct r; pioa_dist_tac.
  destruct b0; pioa_dist_tac.
  destruct b0; pioa_dist_tac.
  destruct b0; pioa_dist_tac.
  destruct b0; pioa_dist_tac.
Qed.

Definition Funct := mkPIOA _ _ funct_data funct_spec.

Lemma compatAB : compatible playerA playerB.
  done.
Qed.

Lemma compatABF : compatible (playerA ||| playerB) Funct.
  done.
Qed.

Definition rpshide : seq (cdom RPSContext) :=
  [:: (commit, true); (commit, false);
      (committed, true); (committed, false);
      (open, true); (open, false);
      (reveal, true); (reveal, false)].

Definition IRPS : PIOA RPSContext (RPSContext |c_ rpshide).
  eapply changeH.
  apply (hidePIOA (playerA ||| playerB ||| Funct) rpshide).
  done.
  apply ctx_is_empty_l.
  apply ctx_symm.
  apply ctx_is_empty_l.
  apply ctx_symm; apply empty_plus_r.
Defined.

Definition FReal (wh : bool) (s : option play * bool) (a : action emptyCtx + action RPSContext) :=
  match a with
  | inr (existT (commit, b) m) =>
    if wh == b then Some (ret (set _1 (if s.1 == None then Some m else s.1) s)) else None
  | inr (existT (committed, b) m) =>
    if (wh == b) && (s.1 != None) then Some (ret s) else None
  | inr (existT (open, b) m) =>
    if (wh == b) then Some (ret set _2 true s) else None
  | inr (existT (reveal, b) m) =>
    if (wh == b) && (s.2) && (s.1 == Some m) then Some (ret s) else None
  | _ => None 
                                                                      end.
                      
Definition FAB_data (wh : bool) : PIOA_data RPSContext emptyCtx.
econstructor.
apply ((None, false)  : option play * bool).
    apply [:: (commit, wh); (open, wh)].
apply    [:: (committed, wh); (reveal, wh)].
apply (FReal wh).
Defined.

Definition FAB_spec (wh : bool) : PIOA_spec (FAB_data wh).
  constructor.
  done.
  done.
  intros; eapply (decide_ad_vP RPSContext emptyCtx _ [finType of option play * bool] _ _ s).
  apply H.
  apply H0.
  done.
  case wh; vm_compute; done.

  intros; eapply decide_i_aP.
  apply H.
  case wh; vm_compute; done.
  intros; simpl.
  move: H; simpl; rewrite /FReal.
  destruct a; rewrite //=; destruct a; destruct x; destruct r; pioa_dist_tac.
Qed.

Definition FA := mkPIOA _ _ (FAB_data false) (FAB_spec false).
Definition FB := mkPIOA _ _ (FAB_data true) (FAB_spec true).

Definition RRPS : PIOA RPSContext (RPSContext |c_ rpshide).
  eapply changeH.
  apply (hidePIOA (playerA ||| playerB ||| FA ||| FB) rpshide).
  done.

  apply ctx_is_empty_l.
  apply ctx_symm; apply ctx_is_empty_l.
  apply ctx_symm; apply ctx_is_empty_l.
  apply ctx_symm; apply empty_plus_r.
Defined.


Definition R_RPS (x : St RRPS) : St IRPS :=
  (x.1.1.1, x.1.1.2, PlayerSt x.1.2.1 x.2.1 x.1.2.2 x.2.2).


Ltac app_v_comp_l_ext_tac :=
  rewrite app_v_comp_l_ext; [ idtac | done | done | done].

Ltac app_v_comp_r_ext_tac :=
  rewrite app_v_comp_r_ext; [ idtac | done | done | done].

Ltac app_v_comp_l_int_tac :=
  rewrite app_v_comp_l_int; [ idtac | done | done | done].

Ltac app_v_comp_r_int_tac :=
  rewrite app_v_comp_r_int; [ idtac | done | done | done].

Ltac caseof_tac b t1 t2 :=
  match (eval cbv in b) with
  | true => t1
  | false => t2
               end.

Ltac app_v_comp_tac :=
  match goal with
  | [ |- context[app_v (?P ||| ?Q) ?c ?x]] => 
    match (eval cbv in (c \in outputs P))  with
        | true => 
          match (eval cbv in (c \in inputs Q)) with
            | true => app_v_comp_l_int_tac
            | false => app_v_comp_l_ext_tac
                         end
        | false => 
          match (eval cbv in (c \in inputs P)) with
            | true => app_v_comp_r_int_tac
            | false => app_v_comp_r_ext_tac
                         end
  end
    end.

Lemma rps_sim : SimpleStateInj RRPS IRPS R_RPS.
  constructor.
  done.
  simpl => x c Hc.
  rewrite /RRPS /IRPS; simpl.
  rewrite !appv_changeh.
  rewrite !appv_hide.
  move: Hc.
  move/inP.
  split_In.
  repeat app_v_comp_tac; rewrite !measE; apply mbind_eqP => y Hy; rewrite !measE //=.
  repeat app_v_comp_tac; rewrite !measE; apply mbind_eqP => y Hy; rewrite !measE //=.

  move => x h.
  rewrite /RRPS /IRPS.
  rewrite apph_changeh.
  rewrite apph_changeh.
  simpl.
  rewrite app_h_hidden.
  rewrite app_h_hidden.

  destruct h as [h H]; simpl; move: H.
  rewrite /rpshide; move/inP; split_In; repeat app_v_comp_tac; rewrite !measE //=.


  elim: (app_vP playerB (commit, true) x.1.1.2); last by done.
  move => m mu Heq ->; rewrite !measE; munder (rewrite !measE /R_RPS //=). done.
  move => _ ->; rewrite !measE //=.

  elim: (app_vP playerA (commit, false) x.1.1.1); last by done.
  move => m mu Heq ->; rewrite !measE; munder (rewrite !measE /R_RPS //=). done.
  move => _ ->; rewrite !measE //=.


  apply (app_v_equienabledP FB Funct); [done | done | idtac | idtac | idtac].
  rewrite /v_chan_equienabled /v_chan_enabled /enabled //=.
  by (exunder (rewrite if_neq_None)).

    simpl => m m' mu mu'; move/eqP; rewrite if_eq_Some => /andP [h1 /eqP h2] /eqP; rewrite if_eq_Some => /andP [h3 /eqP h4]; rewrite -h2 -h4 !measE //= /R_RPS //=.

    move => H; rewrite !measE //=.

  apply (app_v_equienabledP FA Funct); [done | done | idtac | idtac | idtac].
  rewrite /v_chan_equienabled /v_chan_enabled /enabled //=.
  by (exunder (rewrite if_neq_None)).

    simpl => m m' mu mu'; move/eqP; rewrite if_eq_Some => /andP [h1 /eqP h2] /eqP; rewrite if_eq_Some => /andP [h3 /eqP h4]; rewrite -h2 -h4 !measE //= /R_RPS //=.

    move => H; rewrite !measE //=.

  elim: (app_vP playerB (open, true) x.1.1.2); last by done.
  move => m mu Heq ->; rewrite !measE; munder (rewrite !measE /R_RPS //=). done.
  move => _ ->; rewrite !measE //=.

  elim: (app_vP playerA (open, false) x.1.1.1); last by done.
  move => m mu Heq ->; rewrite !measE; munder (rewrite !measE /R_RPS //=). done.
  move => _ ->; rewrite !measE //=.

  apply (app_v_equienabledP FB Funct); [done | done | idtac | idtac | idtac].
  rewrite /v_chan_equienabled /v_chan_enabled /enabled //=.
  by (exunder (rewrite if_neq_None)).

    simpl => m m' mu mu'; move/eqP; rewrite if_eq_Some => /andP [h1 /eqP h2] /eqP; rewrite if_eq_Some => /andP [h3 /eqP h4]; rewrite -h2 -h4 !measE //= /R_RPS //=.

 rewrite /app_i //=.
 remember (val2 x.1.1.1) as v2; destruct v2; rewrite -Heqv2 //=.
 rewrite !measE //=.
 rewrite !measE //=.
 move/andP: h1 => [h11 h12].
 move/andP: h3 => [h31 h32].
 rewrite -(eqP h12) -(eqP h32) //=.
 rewrite !measE //=.


  apply (app_v_equienabledP FA Funct); [done | done | idtac | idtac | idtac].
  rewrite /v_chan_equienabled /v_chan_enabled /enabled //=.
  by (exunder (rewrite if_neq_None)).

    simpl => m m' mu mu'; move/eqP; rewrite if_eq_Some => /andP [h1 /eqP h2] /eqP; rewrite if_eq_Some => /andP [h3 /eqP h4]; rewrite -h2 -h4 !measE //= /R_RPS //=.
    rewrite /app_i //=.
 remember (val2 x.1.1.2) as v2; destruct v2; rewrite -Heqv2 //=.
 rewrite !measE //=.
 rewrite !measE //=.
 move/andP: h1 => [h11 h12].
 move/andP: h3 => [h31 h32].
 rewrite -(eqP h12) -(eqP h32) //=.

 rewrite !measE //=.


  (* for app_i, we may simply compute on the transition function since we know the action. *)
  move => x.
  elim; simpl => c m Hc.
  move: Hc m.
  move/inP.
  split_In; simpl; rewrite /app_i //= => m.
  remember (val1 x.1.1.1) as v1; destruct v1; rewrite -Heqv1 //=;
  rewrite !measE /R_RPS //=.
  remember (val1 x.1.1.2) as v1; destruct v1; rewrite -Heqv1 //=;
  rewrite !measE /R_RPS //=.

Qed.
