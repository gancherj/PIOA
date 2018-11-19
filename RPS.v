
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Aux PIOA Ascii String SSRString FastEnum.
Open Scope string_scope.

Check mkPIOA.


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

Lemma rps_fe : FastEnum.axiom _ [:: choose; committed; reveal; commit; open; winner].
 apply uniq_perm_eq; rewrite ?enum_uniq //= => x; case x; rewrite mem_enum //=.
Qed.

Canonical rps_fetype := FastEnumType RPSContextM (FastEnumMixin _ _ rps_fe).

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

Check FastEnum.axiom.

Lemma play_fe : FastEnum.axiom _ [:: rock; paper; scissors].
  apply uniq_perm_eq; rewrite ?enum_uniq //= => x; case x; rewrite mem_enum //=.
Qed.

Canonical play_fastEnumType:= FastEnumType play (FastEnumMixin _ _ play_fe).

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

Print context.

(* to put in FastEnum *)
Definition unit_fe : FastEnum.axiom _ [:: tt].
  apply uniq_perm_eq.
  done.
  rewrite enum_uniq //=.
  case; rewrite mem_enum //=.
Qed.

Canonical unit_feType := FastEnumType unit (FastEnumMixin _ _ unit_fe).

Definition RPSContext_f (x : RPSContextM * bool) : fastEnumType  :=
  match x.1 with
    | (choose) => [fastEnumType of play]
    | (committed) => [fastEnumType of unit]
    | (reveal) => [fastEnumType of play]
    | (commit) => [fastEnumType of play]
    | (open) => [fastEnumType of unit]
    | (winner) => [fastEnumType of option bool]
                            end.

Definition RPSContext :=
  mkCon ([fastEnumType of RPSContextM * bool])%type RPSContext_f.

Definition emptyContext :=
  mkCon [fastEnumType of unit] (fun _ => [fastEnumType of unit]).

Definition playerSt := (option play * option play * bool * bool)%type.

  

Definition player_trans (wh : bool) (s : playerSt) (a : action emptyContext + action RPSContext) : option {meas playerSt}:=
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
  
Definition playerA : PIOA RPSContext emptyContext.
  eapply mkPIOA.
  apply ((None, None, false, false) : playerSt).
  instantiate (2 := [:: (choose, true); (committed, false); (reveal, false)]).
  instantiate (1 := [:: (commit, true); (open, true); (winner, true)]).
  done.
  instantiate (1 := (player_trans true)).
  done.
  apply/decide_ad_vP.
  by vm_compute.
  apply/decide_i_aP.
  by vm_compute.
Defined.

Definition playerB : PIOA RPSContext emptyContext.
  eapply mkPIOA.
  apply ((None, None, false, false) : playerSt).
  instantiate (2 := [:: (choose, false); (committed, true); (reveal, true)]).
  instantiate (1 := [:: (commit, false); (open, false); (winner, false)]).
  done.
  instantiate (1 := (player_trans false)).
  done.
  apply/decide_ad_vP.
  by vm_compute.
  apply/decide_i_aP.
  by vm_compute.
Defined.

Definition Ftrans (s : playerSt) (a : action emptyContext + action RPSContext) : option {meas playerSt} :=
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
                                                          
Definition Funct : PIOA RPSContext emptyContext.
  eapply mkPIOA.
  apply ((None, None, false,false) : playerSt).
  instantiate (2 := [:: (commit, true); (commit, false); (open, true); (open, false)]). 
  instantiate (1 := [:: (committed, true); (committed, false); (reveal, true); (reveal, false)]).
  done.
  instantiate (1 := Ftrans).
  done.
  apply/decide_ad_vP.
  by vm_compute.
  apply/decide_i_aP.
  by vm_compute.
Defined.
