
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Aux PIOA Ascii String CompPIOA SSRString FastEnum Action Refinement StateSim Compute.
Open Scope string_scope.

Check mkPIOA.

Print pick.
Check pickP.


Definition ctx_bij_trans {C D E : ctx} (H1 : C ~~ D) (H2 : D ~~ E) : C ~~ E.
  apply (Bij C E (fun x => lr H2 (lr H1 x)) (fun y => rl H1 (rl H2 y))).
  move => x; rewrite !(lr_can) //=.
  move => y; rewrite !(rl_can) //=.
  move => c.
  rewrite (ctx_eq H1) (ctx_eq H2) //=.
Defined.

Definition ctx_is_empty_l {C D : ctx} (H : C ~~ emptyCtx) : D ~~ (C :+: D).
 apply (Bij D (C :+: D) (fun x => inr x) (fun x => match x with | inl a => match (lr H a) with end | inr a => a end)).
 done.
 case => a; rewrite //=.
 generalize (H *c a).
 case.
 move => x; simpl.
 done.
Defined.

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

Definition playerSt := (option play * option play * bool * bool)%type.

Definition player_trans (wh : bool) (s : playerSt) (a : action emptyCtx + action RPSContext) : option {meas playerSt}:=
  let vme := s.1.1.1 in
  let vother := s.1.1.2 in
  let cme := s.1.2 in
  let cother := s.2 in
  match a with
  | inr (existT (choose, b) msg) =>
        if (wh == b) then
        Some (ret (if vme == None then Some msg else vme, vother, cme, cother))
        else None
  | inr (existT (commit, b) msg) =>
        if (wh == b) && (vme == Some msg) then
        Some (ret (vme, vother, true, cother))
        else None
  | inr (existT (committed, b) msg) =>
        if (wh != b) then
        Some (ret (vme, vother, cme, true))
        else None
  | inr (existT (open, b) msg) =>
        if (wh == b) && cme && cother then
        Some (ret s)
        else None
  | inr (existT (reveal, b) msg) =>
        if (wh != b) then
        Some (ret (vme, if vother == None then Some msg else vother, cme, cother))
        else None
  | inr (existT (winner, b) msg) =>
    multiIf [::
        ([&& wh == b, msg == Some true & rps_win_a vme vother], (ret s)) ;
        ([&& wh == b, msg == Some false & rps_win_b vme vother], (ret s)) ;
        ([&& wh == b, msg == None & rps_win_tie vme vother], (ret s)) ]
  | _ => None                                                                                          
      end.

Definition player_data (wh : bool) : PIOA_data RPSContext emptyCtx.
econstructor.
apply ((None, None, false, false) : playerSt).
apply ([:: (choose, wh); (committed, ~~ wh); (reveal, ~~ wh)]).
apply ([:: (commit, wh); (open, wh); (winner, wh)]).
apply (player_trans wh).
Defined.

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
Qed.
  

Definition playerA := mkPIOA _ _ (player_data false) (player_spec false).
Definition playerB := mkPIOA _ _ (player_data true) (player_spec true).

Check act.


Goal act playerA (inr (commit, true)) (initDist playerA) = initDist playerA.
simpl.
rewrite ret_bind //=.
rewrite /app_ova.


Definition Ftrans (s : playerSt) (a : action emptyCtx + action RPSContext) : option {meas playerSt} :=
  let va := s.1.1.1 in
  let vb := s.1.1.2 in
  let opa := s.1.2 in
  let opb := s.2 in
  match a with
  | inr (existT (commit, false) msg) =>
    Some (ret (if va == None then Some msg else va, vb, opa, opb))
  | inr (existT (commit, true) msg) =>
    Some (ret (va, if vb == None then Some msg else vb, opa, opb))
  | inr (existT (committed, false) _) =>
    if va != None then Some (ret s) else None
  | inr (existT (committed, true) _) =>
    if vb != None then Some (ret s) else None
  | inr (existT (open, false) _) =>
    Some (ret (va, vb, true, opb))
  | inr (existT (open, true) _) =>
    Some (ret (va, vb, opa, true))
  | inr (existT (reveal, false) x) =>
    if (opa && (va == Some x)) then Some (ret s) else None
  | inr (existT (reveal, true) x) =>
    if (opb && (vb == Some x)) then Some (ret s) else None
  | _ => None end.

Definition funct_data : PIOA_data RPSContext emptyCtx.
econstructor.
apply ((None, None, false, false) : playerSt).
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
  let val := s.1 in
  let op := s.2 in
  match a with
  | inr (existT (commit, b) m) =>
    if wh == b then Some (ret (if val == None then Some m else val, op)) else None
  | inr (existT (committed, b) m) =>
    if (wh == b) && (val != None) then Some (ret s) else None
  | inr (existT (open, b) m) =>
    if (wh == b) then Some (ret (val, true)) else None
  | inr (existT (reveal, b) m) =>
    if (wh == b) && op && (val == Some m) then Some (ret s) else None
  | _ => None end.                                                                   
                      
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
  match x with
  | (xa, xb, (fa1, fa2), (fb1, fb2)) =>
    (xa, xb, (fa1, fb1, fa2, fb2))
      end.

Lemma act_bind' {G D : ctx} {A : choiceType} (P : PIOA G D) (a : H P + C P) (m : {meas A}) (f : A -> {meas (St P) * (trace P)}) :
  act P a (x <- m; f x) = (x <- m; act P a (f x)).
  rewrite /act; case a => x; by rewrite mbindA.
Qed.

Ltac split_tac :=
  match goal with
    | [ H : is_true (_ \in (_ :: _)) |- _ ] => rewrite in_cons in H; elim (orP H); clear H; [move /eqP => -> | move => H]; split_tac
    | [ H : is_true (_ \in nil) |- _ ] => done
    | _ => idtac
                                            end.

Lemma rps_sim : SimpleStateInj RRPS IRPS R_RPS.
  constructor.
  done.
  move => mu hc Hlc.
  rewrite act_bind.
  case hc.
  case => h Hh.
  have H := Hh; move: Hh.
  rewrite /rpshide in H.

  split_tac => Hh; simpl; rewrite !mbindA; apply mbind_eqP => x Hx; simpl in *. 
  rewrite app_h_compP /app_h_comp.
  destruct x.
  
  have Hpi: p \in fastEnum.
  apply mem_fastEnum.
  lazy.

  native_compute in Hpi.
  rewrite //= in Hpi.
  apply/eqP.
  move: x Hx.
  move
  Check forall_fast
  simpl.
  destruct x.
  have eqp: p  = start RRPS by admit.
  subst.
  simpl.
  rewrite app_h_compP /app_h_comp //=.
  rewrite /app_h_comp.
  rewrite /achoose_h_comp.
  vm_compute.
  simpl.
  vm_compute app_h_comp.
  Check act.
  Print act.
  (* TODO: at this point, I need to have a mechanism for concretely computing app_h/ app_ova *)
  rewrite /app_h.
  simpl.
  s
  have: x.1 = start RRPS.
  admit.


  rewrite !mbindA.

  simpl.
  move: Hh.
  rewrite in_cons in H; elim (orP H); clear H; [ move/eqP => -> | move => H].
  admit.
  admit.
  elim (
  clear Hh.
  split_tac.

  case => h Hh.
  rewrite /rpshide in Hh.



  
  intros.
  rewrite act_bind.


  Focus 2.


  admit.

  rewrite act_bind.
  move => mu hc.
  rewrite act_bind'.
  intro.
  symmetry.
  Check act_bind.
  rewrite (act_bind IRPS).
  Check act_bind.

  Set Printing All.
  Check (@act_bind RPSContext (RPSContext |c_ rpshide) [choiceType of (St RRPS * trace RRPS)%type] IRPS hc mu (fun x => ret (R_RPS x.1, x.2))).
  unfold act.
  elim hc.
  rewrite /act.

  Check act_bind.
  rewrite (act_bind IRPS hc mu).

  intro; etransitivity; last first.

  symmetry; apply act_bind.
  simpl.
  apply act_bind.

  etransitivity.
  apply erefl.
  sy
  rewrite (act_bind IRPS hc).

  Check act_bind.
  intro h.
  Set Printing All.
  Check (act_bind' IRPS hc mu (fun x => ret (R_RPS x.1, x.2))).

  rewrite /act.
  Check act_bind.

  rewrite act_bind.
  destruct hc.

  have Hs: (ssval s) \in  rpshide.
  destruct s; rewrite //=.

  remember (ssval s) as h.
  rewrite /rpshide in Hs.

  rewrite in_cons in Hs; elim (orP Hs); clear Hs => Hh.
  Check act_bind.
  rewrite (act_bind (IRPS) (inl s)
  rewrite /rpshide in_cons in Hs.
  Set Ltac Profiling.
  Check (orP Hs).
  elim (orP Hs).
  Show Ltac Profile.
  elim (orP Hs).
  move/eqP => Hh.
  rewrite act_bind.
  move/orP: Hs.

  destruct s as [ h Hh].
  have H := Hh.
  rewrite /rpshide in_cons in H.
  move/orP: H.
  elim.
  move/eqP => eqH; move: Hh.
  rewrite eqH.
  

  Set Printing All.
  case.
  case.
  rewrite /rpshide.
  move => h Hh.
  simpl.
  have Hh2 := Hh.
  rewrite in_cons in Hh2.
  move/orP: Hh2.
  elim.
  move/eqP => eqh.
  simpl.
  move: Hh.
  rewrite eqh => Hh _.
  rewrite !mbindA.
  apply mbind_eqP => y Hy.
  rewrite ret_bind !mbindA //=.

  rewrite /app_h.
  Print achoose_h.
  SearchAbout achoose_h.
  simpl.
  
  vm_compute.


  rewrite /RRPS; simpl.
  simpl.
  rewrite simpl.
  Set Printing All.
  rewrite /rpshide in Hh.
