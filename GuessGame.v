
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems DirectSim StateSim.
Require Import fset.
Require Import Strings.String.
Require Import string.

Local Open Scope string_scope.

(*

Definition guessQ := [eqType of option bool * option bool * bool].

Definition guessTr (which : bool) (x : guessQ) (a : string * option bool) : option (Meas guessQ) :=
  if a.1 == "choose" then
    match x, a.2 with
    | (None, None, false), None => Some (b <- unif (true :: false :: nil); ret (Some b, None, false))
    | _, _ => None
    end
  else if a.1 == "input" then
         match x, a.2 with
         | (Some x, None, false), (Some y) =>
           if which then Some (ret (Some x, Some x, false)) else
             if x == y then Some (ret (Some x, Some true, false)) else Some (ret (Some x, Some false, false))
         | _, _ => Some (ret x)
                        end
       else if a.1 == "output" then
              match x, a.2 with
              | (Some x, Some b, false), (Some b') => if b == b' then Some (ret (Some x, Some b, true)) else None
              | _, _ => None
                          end else None.

Lemma guessTr_subDist wh x a m : guessTr wh x a = Some m -> isSubdist m.
  intro.
  rewrite /guessTr //= in H.
  caseOn (a.1 == "choose"); intro Heq;
    [ rewrite Heq in H | rewrite (negbTE Heq) in H; 
        caseOn (a.1 == "input"); intro Heq2; [ rewrite Heq2 in H | rewrite (negbTE Heq2) in H; 
            caseOn (a.1 == "output"); intro Heq3; rewrite ?Heq3 ?(negbTE Heq3) in H ] ];
  destruct wh;
  destruct x as [ [u v] w];
  destruct u as [ [ | ] | ];
  destruct v as [ [ | ] | ];
  destruct w as [ | ]; destruct a.2; try congruence; try ltac:(injection H; intro; subst); dsubdist.

  apply isDist_isSubdist; apply unif_isDist; done.
  intro; dsubdist.
  apply isDist_isSubdist; apply unif_isDist; done.
  intro; dsubdist.
  destruct b; simpl in H; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; try congruence; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; try congruence; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; try congruence; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; try congruence; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; try congruence; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; try congruence; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; try congruence; injection H; intro; subst; dsubdist.
  destruct b; simpl in H; try congruence; injection H; intro; subst; dsubdist.
Qed.
 
Definition guesspre wh : prePIOA := mkPrePIOA [choiceType of string * option bool] [finType of guessQ] (None, None, false) (guessTr wh) (guessTr_subDist wh).


Definition guessPIOA (wh : bool) : @PIOA [choiceType of string * option bool].
  econstructor.
  instantiate (3 := (fun b => ("input", Some b)) `@` [fset true; false]).
  instantiate (2 := [fset (fun b => ("output", Some b)) `@` [fset true; false]]).
  instantiate (1 := [fset [fset ("choose", None)]]).


  constructor.
  move=> x; rewrite !in_fset => eqx; apply/fdisjointP; move=> y.
  move/fimsetP; elim; intros; subst.
  rewrite (eqP eqx).
  apply/fimsetP; elim.
  congruence.

  move=> x; rewrite !in_fset => eqx; apply/fdisjointP => y;
   move/fimsetP; elim; intros; subst; rewrite (eqP eqx) in_fset //=.

  move=> x y; rewrite !in_fset; move/eqP; intro; subst; move/eqP; intro; subst;
  apply/fdisjointP => z; rewrite !in_fset; move/fimsetP; elim; intros; subst; done.

  move=> x y; rewrite !in_fset; move/eqP; intro; subst; move/eqP; intro; subst.
  rewrite eq_refl //=.

  move=> x y; rewrite !in_fset; move/eqP; intro; subst; move/eqP; intro; subst.
  rewrite eq_refl //=.

  instantiate (1 := guesspre wh).

  move=> T; rewrite in_fset; move/orP; elim; rewrite in_fset; move/eqP; intro; subst.
  move=> s x y; move/fimsetP; elim; intros; subst.
  move/fimsetP: H1; elim; intros; subst.
  
  destruct s as [ [ [ [ ] | ] [ [ | ] | ] ] [ | ] ]; rewrite /enabled //=;
  rewrite /guessTr eq_refl //=; destruct x0, x; simpl; rewrite ?eq_refl in H2; done.

  move=> s x y; rewrite !in_fset.
  move/eqP; intro; subst; move/eqP; intro; subst; done.

  move=> s x; move/fimsetP; elim; intros; subst.
  destruct wh; destruct s as [ [ [ [ ] | ] [ [ | ] | ] ] [ | ] ]; destruct x0; rewrite /enabled //=.


  destruct wh; destruct s as [ [ [ [ ] | ] [ [ | ] | ] ] [ | ] ]; rewrite /enabled /guessTr //=.

  rewrite /guessTr.
  intro.

  caseOn (x.1 == "choose").
  intro Heq; rewrite Heq.
  done.
  caseOn (x.1 == "input")
  simpl.
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



*)