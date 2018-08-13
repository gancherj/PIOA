
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems DirectSim StateSim.

Check enabled.

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

Definition guessTr (which : bool) (x : guessQ) (a : Action) : option (Meas guessQ) :=
  match x, a with
  | (None, None, false), Choose => Some (b <- 
                            unif (true :: false :: nil); ret (Some b, None, false))
  | (Some x, None, false), Input y =>
    if which then Some (ret (Some x, Some x, false)) else
        if x == y then Some (ret (Some x, Some true, false)) else Some (ret (Some x, Some false, false))
  | (Some x, Some b, false), Output b' => if b == b' then Some (ret (Some x, Some b, true)) else None
  | _, Input _ => Some (ret x)
  | _, _ => None
                end.
    

Lemma guessTr_subDist wh x a m : guessTr wh x a = Some m -> isSubdist m.
  destruct wh;
  destruct x as [ [u v] w];
  destruct u as [ [ | ] | ];
  destruct v as [ [ | ] | ];
  destruct w as [ | ];
  destruct a as [ | [ | ] | [ | ] ];
  simpl; try congruence;
    try ltac:(intro H; injection H; intro; subst); dsubdist.
  apply isDist_isSubdist; apply unif_isDist; done.
  intros; dsubdist.
  apply isDist_isSubdist; apply unif_isDist; done.
  intros; dsubdist.
Qed.   
 
Definition guesspre wh : prePIOA := mkPrePIOA [finType of Action] [finType of guessQ] (None, None, false) (guessTr wh) (guessTr_subDist wh).


Definition guessPIOA (wh : bool) : @PIOA [finType of Action].
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

  instantiate (1 := guesspre wh).
  move=> T; rewrite in_set; move/orP; elim; rewrite in_set; move/eqP; intro; subst.
  move=> s x y; rewrite !in_set; move/orP; elim; move/eqP; intro; subst.
  move/orP; elim.
  move/eqP; intro; subst; done.
  move/eqP; intro; subst.
  destruct s as [ [ [ [ ] | ] [ [ | ] | ] ] [ | ] ]; rewrite /enabled //=.
  move/orP; elim.
  move/eqP; intro; subst.
  destruct s as [ [ [ [ ] | ] [ [ | ] | ] ] [ | ] ]; rewrite /enabled //=.
  move/eqP; intro; subst; done.
  move=> s x y; rewrite !in_set.
  move/eqP; intro; subst; move/eqP; intro; subst; done.
  move=> s x; rewrite !in_set; move/orP; elim; move/eqP; intro; subst.
  destruct wh; destruct s as [ [ [ [ ] | ] [ [ | ] | ] ] [ | ] ]; rewrite /enabled //=.
  destruct wh; destruct s as [ [ [ [ ] | ] [ [ | ] | ] ] [ | ] ]; rewrite /enabled //=.
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
  Context (Hcompat : Compatible (guessPIOA true) A).
  Context (Hcompat2 : Compatible (guessPIOA false) A).

  Definition Guess1 := compPIOA (guessPIOA true) A Hcompat.
  Definition Guess2 := compPIOA (guessPIOA false) A Hcompat2.

  Context (icg1 : inputClosed Guess1).
  Context (icg2 : inputClosed Guess2).

  Definition guessTaskCorr : Task Guess2 -> Task Guess1.
    intro T; destruct T.
    econstructor.
    simpl.
    simpl in i.
    apply i.
  Defined.

  Definition guessStateCorr : pQ Guess2 -> pQ Guess1.
    refine (fun p => (_, p.2)).
    destruct p.
    apply (
              match s with
              | (_, _, true) => s 
              | (None, None, false) => s
              | (Some x, None, false) => s
              | (Some x, Some b, false) => (Some x, Some x, false)
              | (None, Some b, false) => s
                                           end).
  Defined.

  Lemma guessActionEquiv : action (guessPIOA true) = action (guessPIOA false).
    rewrite /action //=.
  Qed.

  Lemma guessInAction (a : Action) b : a \in cover (action (guessPIOA b)).
    rewrite /cover !bigcup_setU; destruct a.
    apply/setUP; right; rewrite big_set1 in_set //=.
    apply/setUP; left.
    apply/setUP; left.

    simpl.
    rewrite big_set1; destruct b0; apply/setUP; [left | right]; rewrite in_set //=.
    apply/setUP; left; apply/setUP; right.
    simpl.
    rewrite big_set1; destruct b0; apply/setUP; [left | right]; rewrite in_set //=.
  Qed.
  
  Lemma guessSim : @refinement _ Guess2 Guess1 icg2 icg1 0.
  eapply stateSimSound.
  instantiate (1 := guessStateCorr).
  constructor.
  done.
  intros.
  exists (guessTaskCorr T :: nil).
  simpl.
  destruct T.
  simpl in i.
  rewrite /appTask.
  symmetry in H.
  rewrite (measBind_cong_l H).
  rewrite /meas_fmap.
  rewrite !bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet.
  simpl.
  rewrite /runTask.
  simpl.
  have: forall x0, enabled (comp_prePIOA (guessPIOA false) A) x.1 x0 =
                  enabled (comp_prePIOA (guessPIOA true) A) (guessStateCorr x.1) x0.
  rewrite /enabled.
  intros.
  destruct x.
  simpl.
  rewrite //= /prePIOA_comptrans.
  rewrite !guessInAction.
  simpl.
  
  destruct s as [ [ [ [ [ ] | ] [ [ | ] | ] ] [ | ] ] advs ] ; rewrite //=.
  destruct x0.
  destruct (tr A advs Choose); rewrite //=.
  remember (tr A advs (Input b)) as o; destruct o; rewrite -Heqo; rewrite //=.
  caseOn (Input b \notin cover (action A)).
  intro Hc; rewrite Hc.
  done.
  rewrite negbK.
  intro Hc; rewrite Hc.
  done.
  destruct b.
  simpl.
  
  remember (tr A advs (Output true)) as o; destruct o; rewrite -Heqo; rewrite //=.
  
  destruct (Input b \notin cover (action A)).
  rewrite !guessInAction //=.
  

  destruct (tr A advs (Input b)); rewrite //=.

  simpl.
  done.
  
  destruct x0.
  rewrite guessActionEquiv.
  have: Choose \in cover (action (guessPIOA false)).
  rewrite /cover /action !bigcup_setU.
  apply/setUP; right; simpl.
  rewrite big_set1 in_set //=.
  intro He; rewrite He.
  done.


  have: cover (action (guessPIOA false)) = cover (action (guessPIOA true)).
  rewrite /cover /action //=.
  intro He; rewrite He.
  remember (tr A advs Choose).
  destruct o; rewrite -Heqo.
  rewrite actionEquiv.

  rewrite /cover.
  case

  destruct (tr A advs Choose).
  

  destruct s as [ [ [ ] ] ].
  elim (setUP i).
  move/setUP; elim.
  admit.
  intro; rewrite /appTask.
  rewrite /runTask.
  simpl.
  symmetry in H; symmetry.
  rewrite (measBind_cong_l H).
  rewrite /meas_fmap.
  rewrite !bindAssoc.
  
  

  in
  
  


Inductive GuessSpec (ts : seq (Task Guess)) : Prop:=
| GuessSpec1 : (exists (mu : Meas (pQ A)),
                   runPIOA _ ts (startTr _) ~~ (y <- mu; ret ((start guessPIOA, y), nil)) @ 0) -> GuessSpec ts
| GuessSpec2 : GuessSpec ts.

Lemma guessSpec: forall ts, GuessSpec ts.
  Check hiddenP.
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



