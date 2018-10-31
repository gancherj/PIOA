
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Aux PIOA CompPIOA Ascii String SSRString FastEnum.
Open Scope string_scope.

Definition fset_of_seq {A : choiceType} (s : seq A) :=
  foldr (fun a acc => a |` acc)%fset fset0 s.

Lemma fset_of_seq_cons {A : choiceType} (s : seq A) x :
  fset_of_seq (x :: s) = (x |` fset_of_seq s)%fset.
    rewrite /fset_of_seq //=.
Qed.    

Lemma fset_of_seq_cat {A : choiceType} (s1 s2 : seq A)  :
  fset_of_seq (s1 ++ s2) = (fset_of_seq s1 `|` fset_of_seq s2)%fset.
  move: s2.
  induction s1 => s2; rewrite //=.
  rewrite fset0U //=.
  rewrite IHs1.
  rewrite fsetUA //=.
Qed.

Definition fin_forget {A : finType} (x : [finType of A]) : A := x.

Definition channels_of_seqs {A : choiceType} (s : seq (seq A)) : {fset {fset A}} :=
  fset_of_seq (map fset_of_seq s).

Lemma channels_of_seqs_U {A : choiceType} (s1 s2 : seq (seq A)) :
  (channels_of_seqs s1 `|` channels_of_seqs s2)%fset = channels_of_seqs (s1 ++ s2).
  rewrite /channels_of_seqs.
  rewrite map_cat fset_of_seq_cat //=.
Qed.

Lemma all_fset_cover_seq {A : choiceType} (s : seq (seq A)) P :
  all P (flatten s) = all_fset (cover (channels_of_seqs s)) P.
  admit.
Admitted.

Definition fdisj_seq {A : choiceType} (s1 s2 : (seq A)) :=
  all (fun x => all (fun y => x != y) s2) s1.
(*  foldr (fun x acc => acc && foldr (fun y acc2 => acc2 && (x != y)) true s2) true s1. *)

Lemma fdisj_cover_seqP {A : choiceType} (s1 s2 : seq (seq A)) :
  fdisj_seq (flatten s1) (flatten s2) = [disjoint (cover (channels_of_seqs s1))  & (cover (channels_of_seqs s2))]%fset.
  rewrite /fdisj_seq /cover /channels_of_seqs /fset_of_seq.
  admit.
Admitted.

Definition channels_pairwise_disj {A : choiceType} (s : seq (seq A)) :=
  all (fun C => all (fun C' => (C != C') ==> (fdisj_seq C C')) s) s.
(*  foldr (fun C acc => acc && foldr (fun C' acc2 => acc2 && ((C != C') ==> (fdisj_seq C C'))) true s) true s. *)

Lemma channels_pairwise_disjP {A : choiceType} (s : seq (seq A)) :
  channels_pairwise_disj s = all_fset (channels_of_seqs s) (fun C => all_fset (channels_of_seqs s) (fun C' => (C != C') ==> ([disjoint C & C']%fset))).
  admit.
  Admitted.

Definition decide_inputenabled {A : choiceType} (C : seq A) (P : @prePIOA A) :=
  all (fun a => all (fun s => tr P s a != None) (@fastEnum (pQ P))) C.

Lemma decide_inputenabledP {A : choiceType} (C : seq (seq A)) (P : @prePIOA A) :
  decide_inputenabled (flatten C) P = all_fset (cover (channels_of_seqs C)) (fun a => [forall s, tr P s a != None]).
  admit.
Admitted.

Print actionDeterm.

Definition decide_actionDeterm {A : choiceType} (Cs : seq (seq A)) (P : @prePIOA A) :=
  all (fun C => all (fun a => all (fun s => tr P s a ==> (all (fun b => (a != b) ==> (tr P s b == None)) C)) (fastEnum (pQ P))) C) Cs.

Lemma decide_actionDetermP {A : choiceType} (Cs : seq (seq A)) (P : @prePIOA A) :
  decide_actionDeterm Cs P = all_fset (channels_of_seqs Cs) (actionDeterm P).
  admit.
Admitted.

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


Definition RPSAction := (string * (play))%type.

Definition Commit : seq RPSAction := map (fun x => ("commit", x)) [:: rock; paper; scissors].

Definition Open :=  [:: ("open", rock)].

Definition Winner := [:: ("winA", rock); ("winB", rock); ("winNone", rock)].

Definition Choose := (map (fun x => ("choose", x)) [:: rock; paper; scissors]).
Definition Committed  :=  [:: ("committed", rock)].
Definition Reveal :=  (map (fun x => ("reveal", x)) [:: rock; paper; scissors]).

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

Definition AdvPre : @prePIOA [choiceType of RPSAction].
  econstructor.
  instantiate (1 := ([fastEnumType of ((option play) * (option play) * bool * bool)%type])).
  apply (None, None, false, false).
  apply (channels_of_seqs [:: Commit; Open; Winner]).
  apply (channels_of_seqs [:: Choose; Committed; Reveal]).
  apply fset0.
  refine (
      fun s a =>
        match s with
        | (va, vb, ca, cb) => 
            if (a.1 == "choose") then Some (ret (if va == None then Some a.2 else va, vb, ca, cb))
        else if (a.1 == "commit") then if va == Some a.2 then Some (ret (va, vb, true, cb)) else None
        else if (a.1 == "committed") then Some (ret (va, vb, ca, true)) 
        else if (a.1 == "open") then if (ca && cb) then Some (ret s) else None
        else if (a.1 == "reveal") then Some (ret (va, if vb == None then Some a.2 else vb, ca, cb))
        else if (a.1 == "winA") then if (rps_win_a va vb) then Some (ret s) else None
        else if (a.1 == "winB") then if (rps_win_b va vb) then Some (ret s) else None
        else if (a.1 == "winNone") then if (rps_win_tie va vb) then Some (ret s) else None
        else None
        end).
  Defined.

Lemma AdvWf : PIOA_axiom AdvPre.
  apply/and4P; split.
  apply/and4P; split.
  rewrite /inputs /outputs //=.
  rewrite -fdisj_cover_seqP /fdisj_seq /Choose /Committed /Reveal /Commit /Open /Winner //=.
  rewrite /hiddens //= /cover big_seq_fset0 fdisjointX0 //=.
  rewrite /hiddens //= /cover big_seq_fset0 fdisjointX0 //=.

  rewrite /channels //= !channels_of_seqs_U fsetU0.
  rewrite -channels_pairwise_disjP //=.

  rewrite -decide_inputenabledP; vm_compute; done.



  rewrite /lc_channels fsetU0 //=.
  rewrite -decide_actionDetermP; vm_compute; done.
  

  rewrite -decide_actionDetermP //=; do![unlock enum_mem; rewrite unlock /prod_enum /ord_enum ?insubT].

  Time Eval vm_compute in
      ( [seq (x,y) | x <- [:: true; false], y <- [:: true; false]]).
  Time Eval vm_compute in (enum [finType of (bool * bool)%type]).

  Eval vm_compute in
      ( [seq (x,y,z,w) | x <- [:: true; false], y <- [:: true; false], z <- [:: true; false]; w <- [:: true; false]]).
                      

  Eval vm_compute in (enum (pQ AdvPre)).
  native_compute.

  rewrite //=.
  rewrite /actions /inputs /outputs /hiddens -!coverU fsetU0 channels_of_seqs_U //=.
  rewrite -all_fset_cover_seq.
  rewrite //= /opt_lift //=.
  rewrite -coverU.
  rewrite /all_fset.

  rewrite /actions /inputs /outputs //=.
  rewrite /lc_channels fsetU0//=.

  simpl_enum.
  native_compute.
  Eval vm_compute in (map fin_forget (@Finite.enum [finType of bool])).

  Eval simpl in ((pQ AdvPre)).
  native_compute.


  
  rewrite /channels_pairwise_disj !big_cons !big_nil /Choose /Committed /Reveal /Commit /Open /Winner /fdisj_seq !big_map.
  native_compute.

  rewrite -fdisj_cover_seqP /fdisj_seq /Choose /Committed /Reveal /Commit /Open /Winner !big_cons !big_nil //=.

  Check (fset_of_seq [:: Choose; Commit; Reveal]).
  rewrite -(fdisj_cover_seqP [:: Choose; Commit; Reveal] [:: Commit; Open; Winner]).
  
  rewrite !fdisjointUX; apply/and4P; split; rewrite !fdisjointXU; apply/and4P; split.
  apply/and4P; split.
  rewrite /Reveal.
  apply (is_true_true).
  vm_compute.
  Eval Compute.



  
  apply (
      fset1 [fset ("commit", x) | x in (fset1 0)]]%fset

    ).

  instantiate (1 := ((option play) * (option play) * bool * bool)%bool).
  apply 
