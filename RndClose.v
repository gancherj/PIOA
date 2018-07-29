From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset.
Require Import PIOA Meas Posrat Expansion.

Set Implicit Arguments.
Unset Strict Implicit.


Lemma nseq_rcons {A} (x : nat) (a : A) : nseq (S x) a = rcons (nseq x a) a.
  induction x.
  simpl.
  done.
  simpl.
  rewrite -IHx.
  simpl.
  done.
Qed.

Lemma runPIOA_appTask_nseq {A} (P : @PIOA A) (t : Task P) (n : nat) d :
  runPIOA P (nseq n t) (appTask P t d) =
  appTask P t (runPIOA  P (nseq n t) d).
  induction n.
  done.
  rewrite nseq_rcons.
  rewrite !runPIOA_rcons.
  rewrite IHn.
  done.
Qed.

Lemma finType_bij_enum (A : finType) (f : A -> A) :
  bijective f -> perm_eq (enum A) (map f (enum A)).
  intros.
  rewrite /perm_eq; apply/allP; intros; simpl.
  rewrite count_uniq_mem.
  rewrite mem_enum.
  simpl.
  rewrite -codomE.

  rewrite count_uniq_mem.
  rewrite inj_card_onto.
  done.
  destruct H; eapply can_inj.
  apply H.
  done.
  rewrite /codom.
  rewrite map_inj_uniq.
  apply enum_uniq.
  destruct H; eapply can_inj; apply H.
  apply enum_uniq.
Qed.

Definition unifFin (A : finType) : Meas A :=
  unif (enum A).

Lemma finType_unif_bij (A : finType) (f : A -> A) :
  bijective f ->
  (unifFin A) ~~ (meas_fmap (unifFin A) f) @ 0.
  intros.
  rewrite /measEquiv; intros.
  rewrite /integ.
  rewrite /unifFin.
  rewrite /meas_fmap.
  rewrite /measBind /measJoin /measSum.
  rewrite big_flatten //=.
  rewrite big_map.
  erewrite eq_big_perm.
  instantiate (1 := map f (enum A)).

  rewrite /measScale.
  rewrite /measRet.
  rewrite !big_map.
  rewrite pdist_le0; apply/eqP.
  apply eq_bigr.
  intros.
  rewrite big_map big_cons big_nil.
  apply/eqP; rewrite /eq_op //=.
  destruct (f0 (f i)).
  simpl.
  rewrite GRing.Theory.addr0.
  rewrite GRing.Theory.mulr1.
  done.
  apply finType_bij_enum.
  done.
Qed.



Lemma partition_set1 {A : finType} (s : {set A}) :
  s <> set0 -> partition [set s] s.
  unfold partition; intros; apply/andP; split.
  unfold cover.
  rewrite big_set1.
  apply eq_refl.
  apply/andP;split.
  apply/trivIsetP.
  move=> x y Hx Hy.
  rewrite (set1P Hx).
  rewrite (set1P Hy).
  rewrite eq_refl; done.

  apply/negP.
  move=> Hx.
  rewrite (set1P Hx) in H.
  done.
Qed.

Section RandDefs.
  Context {A : finType}.
  Context (defA : A).
  Context (D1 : Meas A).
  Context (SD : isSubdist D1).
  Context (n : nat).

Inductive Action : Type :=
  | Choose : Action 
  | Output : A -> Action
  | Compute : Action .

Definition sum_of_action (a : Action) :=
  match a with
  | Choose => inl tt
  | Output x => inr (inl x)
  | Compute => inr (inr tt)
                   end.

Definition action_of_sum t :=
  match t with
  | inl tt => Choose
  | inr (inl x) => Output x
  | inr (inr tt) => Compute
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


Definition RndQ := [eqType of option A].
  
Definition RndTr (x : RndQ) (a : Action) : option (Meas RndQ) :=
  match x, a with
  | None, Choose => Some (x <- D1; ret (Some x))
  | Some x, Output y => if x == y then Some (ret (Some x)) else None
  | _, _ => None
              end.

Lemma RndTr_subDist x a m : RndTr x a = Some m -> isSubdist m.
destruct x, a; simpl; try congruence.
case (eqVneq s s0); intro.
subst; rewrite eq_refl.
intro H; injection H; intro; subst.
dsubdist.
rewrite (negbTE i); congruence.
intro H; injection H; intro; subst.
dsubdist.
done.
intros; dsubdist.
Qed.


Definition rndpre : prePIOA := mkPrePIOA [finType of Action] [finType of RndQ] None RndTr RndTr_subDist.


Definition RndH := set1 Choose.
Definition RndI : {set Action} := set0.
SearchAbout (seq _ -> {set _}).
Definition RndO : {set Action} := Output @: A.

Lemma rnd_taskStructure : TaskStructure (rndpre) (RndO ) (RndH ) (set1 (RndO )) (set1 (RndH )).

constructor.


apply partition_set1; apply /eqP /set0Pn; exists (Output defA); apply mem_imset; done.
apply partition_set1; apply /eqP /set0Pn; exists (Choose ); by rewrite in_set.

intros.
rewrite /actionDeterm; intros.

rewrite in_setU in H; move/orP: H => [H | H]; rewrite in_set in H; rewrite (eqP H).
destruct s.
rewrite /enabled.

simpl.
apply/orP; right.
apply/cards1P; exists (Output s); apply setP; move=>x; rewrite !in_set; destruct x; rewrite //=.
rewrite andbF; symmetry; apply/eqP; done.
destruct (eqVneq s s0).
rewrite /RndO.
subst; rewrite !eq_refl andbT.
apply/ imsetP; exists s0; done.
rewrite (negbTE i) andbF; symmetry; apply/eqP.
move/eqP: i; simpl.
congruence.
rewrite andbF; symmetry; apply/eqP; congruence.
apply/orP; left.
rewrite cards_eq0; apply /eqP/setP; move=> x; rewrite in_set0.
destruct x.
rewrite in_set.
rewrite /enabled andbT.
rewrite /RndO.
apply/imsetP; elim; congruence.
rewrite in_set; rewrite /enabled //= andbF //=.
rewrite in_set; rewrite /enabled //= andbF //=.
destruct s.
apply/orP; left.
rewrite cards_eq0; apply/eqP/setP => x; rewrite /RndH in_set in_set0 /enabled //=; elim x.
apply andbF.
intros; rewrite in_set.
apply/andP; elim; move/eqP; congruence.
apply andbF.

apply/orP; right.
rewrite /RndH.
apply/cards1P; exists (Choose).
apply/setP => x.
rewrite !in_set.
destruct x; rewrite /enabled //=.
Qed.




Definition RndPIOA : @PIOA [finType of Action].
econstructor.
apply rnd_taskStructure.
instantiate (1 := RndI).
rewrite /trivIset /cover.
rewrite /RndI /RndO /RndH.
rewrite !bigcup_setU !big_setU1 //=.
rewrite cards0 !big_set1 set0U !cardsU //=.
rewrite !cards1 !big_set0.
rewrite add0n addn0 cards0.
rewrite setI0 setU0 cards0 addn0 subn0.


have : ((@Output ) @: A) :&: [set Choose] = set0.

apply /setP => x; rewrite in_set0; apply/setIP; elim; rewrite !in_set.
intros.
move/imsetP: H; elim; intros.
subst.
move/eqP: H0; congruence.
intro H; rewrite H cards0 subn0.
done.

by rewrite in_set.
rewrite setU0 !in_set.
apply/eqP/setP. 
intro.
have HC := H (Choose).
rewrite in_set eq_refl in HC.
move/imsetP: HC.
elim; congruence.
rewrite setU0 in_set //=.
rewrite negb_or; apply/andP; split; rewrite in_set.
apply/eqP/setP; intro H; have HC := H (Output defA). 
rewrite in_set0 in HC.
symmetry in HC;
move/imsetP: HC.
elim.
exists defA; done.

apply/eqP/setP; intro H; have HC := H (Choose).
rewrite in_set0 in_set eq_refl in HC; done.
intros; rewrite /RndI in H.
rewrite in_set0 in H.
done.

intros.
rewrite !in_setU.
destruct x.
apply/orP; right.
apply/orP; right.
rewrite /RndH in_set; done.
apply/orP; right; apply/orP; left.
rewrite /RndO.
apply/imsetP.
exists s0; done.
destruct s; simpl in H.
done.
done.
Defined.

Definition RndChoose : Task RndPIOA.
  econstructor.
  instantiate (1 := [set Choose]).
  simpl.
  apply/setUP; right; rewrite /RndH.
  rewrite in_set.
  done.
Defined.

Definition RndOutput : Task RndPIOA.
  econstructor.
  simpl; rewrite /RndO.
  instantiate (1 := [set Output x | x : A]).
  apply/setUP; left; rewrite in_set; done.
Defined.

Check runPIOA.


Inductive RndSpec (ts : seq (Task RndPIOA)) : Prop:=
  | RndSpec1 : runPIOA _ ts (startTr _) ~~ runPIOA _ nil (startTr _) @ 0 -> RndSpec ts
  | RndSpec2 : (exists n, runPIOA _ ts (startTr _) ~~ runPIOA _ (RndChoose :: nseq n RndOutput) (startTr _) @ 0 )  -> RndSpec ts.

Lemma rndChooseOutput : forall n, runPIOA RndPIOA (RndChoose :: nseq n RndOutput) (startTr _) ~~
                               (x <- D1; ret (Some x, nseq n (Output x))) @ 0 .
  induction n0.
  simpl; rewrite /appTask /startTr; dsimp.
  case:pickP => x.
  move/andP => [i1 i2]; rewrite in_set in i1; rewrite (eqP i1).
  rewrite /external //= set0U /RndO.
  case:imsetP.
  elim; done.
  intro; dsimp.
  apply measBind_cong_r; intros; dsimp.
  apply measEquiv_refl.
  done.
  have HC := ((x Choose)).
  move/andP: HC; elim.
  rewrite in_set /enabled //=.
  simpl.
  rewrite runPIOA_appTask_nseq.
  drewr (appTask_cong RndPIOA).
  apply IHn0.
  rewrite /appTask; dsimp.
  apply measBind_cong_r; intros; dsimp.
  case:pickP => y.
  move/andP => [y0 y1]. 
  case (imsetP y0); intros; subst.
  rewrite /enabled in y1.
  simpl in y1.
  case (eqVneq x x0).
  intros; subst.
  rewrite eq_refl.
  dsimp.
  rewrite /external //= /RndI /RndO set0U.
  case: imsetP.
  elim; intros; subst; apply measEquiv_refl. 
  elim.
  eexists; rewrite //=.
  intro HC; rewrite (negbTE HC) in y1; done.
  have HC := y (Output x).
  move/andP: HC.
  elim.
  rewrite /enabled //= eq_refl //=.
  split.
  apply/imsetP; eexists; done.
  done.
  done.
Qed.

Lemma rndSpec : forall ts, RndSpec ts.
  induction ts using last_ind.
  apply RndSpec1.
  apply measEquiv_refl.
  destruct IHts.
  destruct x.
  have Hi := i.
  rewrite !in_set in Hi.
  elim: (orP Hi); move/eqP; intro; subst.
  apply RndSpec1.
  rewrite runPIOA_rcons.
  simpl.
  rewrite (appTask_cong _ _ _ _ H) /appTask //=.
  have H2 := @bindRet_r _ (startTr RndPIOA).
  symmetry; etransitivity; symmetry in H2. apply H2.
  apply measBind_cong_r; intros.
  destruct x.
  rewrite /measSupport /measRed /startTr in H0.
  simpl in H0.
  rewrite mem_seq1 in H0; move/eqP: H0 => H0; injection H0; intros; subst.
  simpl.
  case: pickP.
  rewrite //= /RndO.
  move=>x /andP; elim.
  move/imsetP; elim.
  intros; subst.
  done.
  intros; reflexivity.
  rewrite /startTr; dsubdist.

  apply RndSpec2; exists 0%nat.
  simpl.
  rewrite runPIOA_rcons.
  rewrite /RndH.
  rewrite (appTask_cong _ _ _ _ H).
  simpl.
  reflexivity.

  destruct H.
  destruct x.
  have Hi := i.
  rewrite //= !in_set in Hi.
  move/orP: Hi; elim; move/eqP; intro; subst.
  apply RndSpec2; exists (S x0).
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H).
  simpl.
  remember (appTask _ RndChoose (startTr RndPIOA)).
  rewrite -Heqm.
  generalize m.
  clear H.
  induction x0.
  simpl.
  reflexivity.
  simpl; intros.
  rewrite IHx0.
  reflexivity.

  apply RndSpec2; exists x0.
  simpl.
  rewrite (runPIOA_rcons).
  rewrite (appTask_cong _ _ _ _ H).
  rewrite (appTask_cong _ _ _ _ (rndChooseOutput _)).
  have He := rndChooseOutput x0.
  simpl in He.
  symmetry; etransitivity. apply He.
  rewrite /appTask.
  dsimp.
  apply measBind_cong_r; intros.
  dsimp.
  case:pickP => x1.
  move/andP; elim; rewrite /RndH in_set; move/eqP; intro; subst.
  rewrite /enabled.
  simpl.
  done.
  reflexivity.
  done.
Qed.

Lemma RndInputClosed : inputClosed RndPIOA.
  constructor.
Qed.


End RandDefs.

Section RandCloseProof.
  Context {A : finType}.
  Context (defA : A).
  Context (D1 D2 : Meas A).
  Context (HD1 : isSubdist D1).
  Context (HD2 : isSubdist D2).
  Context {e : posrat}.
  Context (HClose : D1 ~~ D2 @ e).
  Check RndPIOA.

  Lemma RndCloseRefine :
    @refinement _ (RndPIOA defA HD1) (RndPIOA defA HD2) (RndInputClosed _ _) (RndInputClosed _ _) e.
    intro.
    destruct (rndSpec ts).
    exists nil.
    eapply measEquiv_sub.
    instantiate (1 := 0). 
    destruct e; done.
    rewrite /traceOf.
    rewrite (fmap_cong _ _ _ _ H).
    reflexivity.

    destruct H.
    exists (RndChoose defA HD2 :: nseq x (RndOutput defA HD2)).
    rewrite /traceOf.
    rewrite -(padd0r e); eapply measEquiv_trans.
    apply fmap_cong.
    apply H.

    rewrite -(padd0r e); eapply measEquiv_trans.
    apply fmap_cong.
    apply rndChooseOutput.
    rewrite -(padd0r e); apply measEquiv_symm; eapply measEquiv_trans.
    apply fmap_cong.
    apply rndChooseOutput.
    rewrite /meas_fmap.
    rewrite -(padd0r e); eapply measEquiv_trans.
    dsimp.
    apply measEquiv_refl.
    rewrite -(padd0r e); apply measEquiv_symm; eapply measEquiv_trans.
    dsimp; apply measEquiv_refl.
    apply measBind_cong_l.
    done.
    intros; dsubdist.
    intros; dsubdist.
Qed.


End RandCloseProof.
