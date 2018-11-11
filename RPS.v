
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Aux PIOA CompPIOA Ascii String SSRString FastEnum.
Open Scope string_scope.






Inductive play := rock | paper | scissors.

Definition play_eq m1 m2 :=
  match m1,m2 with
    | rock,rock => true | paper,paper => true | scissors,scissors => true | _,_ => false end.

Definition play_obool m :=
  match m with
    | rock => None | paper => Some false | scissors => Some true end.

Definition obool_play m :=
  match m with
    | None => Some rock | Some false => Some paper | Some true => Some scissors end.

Lemma play_obool_can : pcancel play_obool obool_play.
  by case.
Qed.

Definition play_enum := [:: rock; paper; scissors].

Canonical play_eqType := EqType play (PcanEqMixin play_obool_can).
Lemma play_finmix : Finite.axiom play_enum.
  rewrite /Finite.axiom; case; rewrite //=.
Qed.
Canonical play_choiceType := ChoiceType play (PcanChoiceMixin play_obool_can).
Canonical play_countType := CountType play (PcanCountMixin play_obool_can).
Canonical play_finType := FinType play (FinMixin play_finmix).
Lemma play_fastenummix : FastEnum.axiom _ play_enum.
  apply uniq_perm_eq.
  rewrite //=.
  apply enum_uniq.
  move => x; case x; rewrite //= mem_enum //=.
Qed.
Canonical play_fastEnumType:= FastEnumType play (FastEnumMixin _ _ play_fastenummix).

                                                                  

Definition RPSAction := (string * bool * (play))%type.

Definition Commit wh : seq RPSAction := map (fun x => ("commit", wh, x)) [:: rock; paper; scissors].
Definition Open (wh : bool) : seq RPSAction :=  [:: ("open", wh, rock)].
Definition Winner (wh : bool) := [:: ("winA", wh, rock); ("winB", wh, rock); ("winNone", wh, rock)].
Definition Choose (wh : bool) := (map (fun x => ("choose", wh, x)) [:: rock; paper; scissors]).
Definition Committed (wh : bool) :=  [:: ("committed", ~~ wh, rock)].
Definition Reveal (wh : bool) :=  (map (fun x => ("reveal", ~~ wh, x)) [:: rock; paper; scissors]).

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

Definition playerO wh : seq (seq RPSAction) := [:: Commit wh; Open wh; Winner wh].
Definition playerI wh : seq (seq RPSAction) := [:: Choose wh; Committed wh; Reveal wh].
Definition playerH : seq (seq RPSAction) := nil.


Definition player_trans (wh : bool) s (a : RPSAction) :=
  let va := s.1.1.1 in
  let vb := s.1.1.2 in
  let ca := s.1.2 in
  let cb := s.2 in
    multiIf [::
               ([&& (a.1.1 == "choose") & (a.1.2 == wh)], ret (if s.1.1.1 == None then Some a.2 else va, vb, ca, cb));
               ([&& (a.1.1 == "commit") , (va == Some a.2) & (a.1.2 == wh)], (ret (va, vb, true, cb)));
               ([&& (a.1.1 == "committed") & (a.1.2 != wh)], (ret (va, vb, ca, true)));
               ([&& (a.1.1 == "open") , ca , cb & (a.1.2 == wh)], (ret s));
               ([&& (a.1.1 == "reveal") & (a.1.2 != wh)], (ret (va, if vb == None then Some a.2 else vb, ca, cb)));
               ([&& (a.1.1 == "winA") , (a.1.2 == wh) & rps_win_a va vb], (ret s));
               ([&& (a.1.1 == "winB") , (a.1.2 == wh) & rps_win_b va vb], (ret s));
               ([&& (a.1.1 == "winB") , (a.1.2 == wh) & rps_win_tie va vb], (ret s)) ].


Definition PlayerA : @PIOA [choiceType of RPSAction].
  mkPIOA_tac (None : option play, None : option play, false, false) (playerO true) (playerI true) playerH (player_trans true).
Defined.

Print PlayerA.

Definition PlayerB : @PIOA [choiceType of RPSAction].
  mkPIOA_tac (None : option play, None : option play, false, false) (playerO false) (playerI false) playerH (player_trans false).
Defined.

Print compatible.

