
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems.

Inductive Action : Type :=
  | Choose : Action 
  | Input : bool -> Action
  | Output : bool -> Action.


Definition sum_of_action (a : Action) :=
  match a with
  | Choose => inl tt
  | Input x => inr (inr x)
  | Output x => inr (inl x)
                   end.

Definition action_of_sum t :=
  match t with
  | inl tt => Choose
  | inr (inr x) => Input x
  | inr (inl x) => Output x
                      end.

Lemma action_cancel : cancel sum_of_action action_of_sum.
  by case.
Qed.

Definition action_eqmix := CanEqMixin action_cancel.
Canonical action_eqType := EqType Action action_eqmix.
Definition action_choicemix := CanChoiceMixin action_cancel.
Canonical action_choiceType := ChoiceType Action action_choicemix.
Definition action_countmix := CanCountMixin action_cancel.
Canonical action_countType := CountType Action action_countmix.
Definition action_finmix := CanFinMixin action_cancel.
Canonical action_finType := FinType Action action_finmix.

Definition guessQ := [eqType of option bool * option bool * bool].

Definition guessTr (x : guessQ) (a : Action) : option (Meas guessQ) :=
  match x, a with
  | (None, None, false), Choose => Some (b <- 
                            unif (true :: false :: nil); ret (Some b, None, false))
  | (Some x, None, false), Input y => if x == y then Some (ret (Some x, Some true, false)) else Some (ret (Some x, Some false, false))
  | (Some x, Some b, false), Output b' => if b == b' then Some (ret (Some x, Some b, true)) else None
  | _, Input _ => Some (ret x)
  | _, _ => None
                end.

Lemma guessTr_subDist x a m : guessTr x a = Some m -> isSubdist m.
  destruct x as [ [u v] w];
  destruct u as [ [ | ] | ];
  destruct v as [ [ | ] | ];
  destruct w as [ | ];
  destruct a as [ | [ | ] | [ | ] ];
  simpl; try congruence;
    try ltac:(intro H; injection H; intro; subst); dsubdist.
  apply isDist_isSubdist; apply unif_isDist; done.
  intros; dsubdist.
Qed.   
 
Definition guesspre : prePIOA := mkPrePIOA [finType of Action] [finType of guessQ] (None, None, false) guessTr guessTr_subDist.



Definition guessPIOA : @PIOA [finType of Action].
  econstructor.
  instantiate (3 := [set Input true; Input false]).
  instantiate (2 := [set [set Output true; Output false]]).
  instantiate (1 := [set [set Choose]]).

  constructor.
  move=> x; rewrite !in_set; intro; apply/disjointP; move=> y; rewrite !in_set.
  rewrite (eqP H) !in_set.
  move/orP; elim; move/eqP; intro; subst; done.

  move=> x; rewrite !in_set; intro; apply/disjointP; move=> y; rewrite !in_set.
  rewrite (eqP H) !in_set.
  move/orP; elim; move/eqP; intro; subst; done.

  move=> x y; rewrite !in_set; move/eqP; intro; subst; move/eqP; intro; subst; apply/disjointP.
  move=> x; rewrite !in_set; move/orP; elim; move/eqP; intro; subst; done.

  move=> x y; rewrite !in_set; move/eqP; intro; subst; move/eqP; intros; subst.
  rewrite eq_refl in H; done.
  move=> x y; rewrite !in_set; move/eqP; intro; subst; move/eqP; intros; subst.
  rewrite eq_refl in H; done.

  instantiate (1 := guesspre).
  move=> T; rewrite in_set; move/orP; elim; rewrite in_set; move/eqP; intro; subst.
  move=> s x y; rewrite !in_set; move/orP; elim; move/eqP; intro; subst.
  move/orP; elim.
  move/eqP; intro; subst; done.
  move/eqP; intro; subst.
  destruct s as [ [ [ [| ] | ]  [ [|] | ] ] [ | ] ]; rewrite /enabled //=.
  move/orP; elim.
  move/eqP; intro; subst.
  destruct s as [ [ [ [| ] | ]  [ [|] | ] ] [ | ] ]; rewrite /enabled //=.
  move/eqP; intro; subst; done.
  move=> s x y; rewrite !in_set.
  move/eqP; intro; subst; move/eqP; intro; subst; done.
  move=> s x; rewrite !in_set; move/orP; elim; move/eqP; intro; subst.
  destruct s as [ [ [ [| ] | ]  [ [|] | ] ] [ | ] ]; rewrite /enabled //=.
  destruct s as [ [ [ [| ] | ]  [ [|] | ] ] [ | ] ]; rewrite /enabled //=.
  destruct x; intros.
  apply/setUP; right.
  apply/bigcupP.
  exists [set Choose]; rewrite in_set //=.
  apply/setUP; left; apply/setUP; left.
  destruct b; apply/setUP; [left | right]; rewrite in_set //=.
  apply/setUP; left; apply/setUP; right.
  apply/bigcupP; exists [set Output true; Output false]; rewrite in_set //=.
  destruct b; apply/orP; [left | right]; rewrite in_set //=.
Defined.

Section GuessComp.
  Context (A : @PIOA [finType of Action]).
  Context (Hcompat : Compatible guessPIOA A).

  Definition Guess := compPIOA guessPIOA A Hcompat.


Inductive GuessSpec (ts : seq (Task Guess)) : Prop:=
| GuessSpec1 : (exists (mu : Meas (pQ A)),
                   runPIOA _ ts (startTr _) ~~ (y <- mu; ret ((start guessPIOA, y), nil)) @ 0) -> GuessSpec ts
| GuessSpec2 : GuessSpec ts.

Lemma guessSpec: forall ts, GuessSpec ts.
  induction ts using last_ind.
  apply GuessSpec1; exists (ret (start A)).
  simpl.
  rewrite /startTr.
  dsimp.
  reflexivity.
  destruct x.
  simpl in i.
  rewrite /mkGuessQ.
  
  rewrite /Guess.
  rewrite /compPIOA.
  rewrite /start.



