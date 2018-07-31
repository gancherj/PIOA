
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA2 Meas Posrat CompPIOA.

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
congruence.
destruct o.
case (eqVneq b b0).
intro; subst; rewrite eq_refl; intro H2; injection H2; subst; intro; subst; dsubdist.
intro H; rewrite (negbTE H); congruence.
case (eqVneq b b0).
intro; subst; rewrite eq_refl; intro H2; injection H2; subst; intro; subst; dsubdist.
intro H; rewrite (negbTE H); congruence.
Qed.

Definition guesspre : prePIOA := mkPrePIOA [finType of Action] [finType of guessQ] (None, false) guessTr guessTr_subDist.
