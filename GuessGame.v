
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA2 Meas Posrat CompPIOA Lems.

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

Definition guessQ := [eqType of option bool * bool].

Definition guessTr (x : guessQ) (a : Action) : option (Meas guessQ) :=
  match x, a with
  | (None, _), Choose => Some (b <- 
                            unif (true :: false :: nil); ret (Some b, false))
  | (Some x, _), Input y => if x == y then Some (ret (Some x, true)) else Some (ret (Some x, false))
  | (None, _), Input y => Some (ret x)
  | (_, b), Output b' => if b == b' then Some (ret x) else None
  | _, _ => None
                end.

Lemma guessTr_subDist x a m : guessTr x a = Some m -> isSubdist m.
destruct x, a; simpl.
destruct o; simpl.
congruence.
intro H; injection H; intro; subst.
dsubdist.
apply isDist_isSubdist.
apply unif_isDist.
done.
intros; dsubdist.
destruct o; simpl.
case (eqVneq b1 b0).
intro; subst; rewrite eq_refl.
intro H; injection H; intro; subst.
dsubdist.
intro H; rewrite (negbTE H).
intro H2; injection H2; intro; subst.
dsubdist.
intro H2; injection H2; intro; subst; dsubdist.
destruct o.
case (eqVneq b b0).
intro; subst; rewrite eq_refl; intro H2; injection H2; subst; intro; subst; dsubdist.
intro H; rewrite (negbTE H); congruence.
case (eqVneq b b0).
intro; subst; rewrite eq_refl; intro H2; injection H2; subst; intro; subst; dsubdist.
intro H; rewrite (negbTE H); congruence.
Qed.

Definition guesspre : prePIOA := mkPrePIOA [finType of Action] [finType of guessQ] (None, false) guessTr guessTr_subDist.



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
  move=> s x; rewrite !in_set; move/orP; elim; move/eqP; intro; subst.
  destruct s; destruct o; destruct b.
  destruct b0; done.
  destruct b0; done.
  done.
  done.
  destruct s; destruct o; destruct b.
  destruct b0; done.
  destruct b0; done.
  done.
  done.


  intros; destruct x.
  apply/setUP; right.
  rewrite /cover.
  apply/bigcupP; exists [set Choose]; rewrite in_set //=.
  apply/setUP; left; apply/setUP; left.
  apply/setUP; destruct b; [left | right]; rewrite in_set //=.
  apply/setUP; left; apply/setUP; right.
  apply/bigcupP.
  exists [set Output true; Output false].
  rewrite in_set //=.
  destruct b; rewrite !in_set //=.
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



