From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset.
Require Import PIOA Meas Posrat Lems.

Set Implicit Arguments.
Unset Strict Implicit.

(*

to adapt

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


Definition RndTH := [set [set Choose] ].
Definition RndI : {set Action} := set0.
Definition RndTO : {set {set Action}} := [set Output @: A].


Definition RndPIOA : @PIOA [finType of Action].
  econstructor.
  instantiate (1 := RndTH).
  instantiate (1 := RndTO).
  instantiate (1 := RndI).
  constructor.
  intros.
  rewrite /RndI.
  rewrite -setI_eq0.
  rewrite set0I; done.
  intros.
  rewrite /RndI.
  rewrite -setI_eq0.
  rewrite set0I; done.
  rewrite /RndTO /RndTH.
  move=> x y;
  rewrite !in_set.
  move/eqP; intro; subst.
  move/eqP; intro; subst.
  apply/disjointP.
  intro; move/imsetP; elim.
  rewrite in_set.
  intros; subst; done.
  rewrite /RndTO.
  move => x y; rewrite !in_set; move/eqP; intro; subst; move/eqP; intro; subst.
  rewrite eq_refl; done.
  rewrite /RndTH.
  move => x y; rewrite !in_set; move/eqP; intro; subst; move/eqP; intro; subst.
  rewrite eq_refl; done.
  instantiate (1 := rndpre).

  move=> T /setUP; elim.
  rewrite /RndTO in_set.
  move/eqP; intro; subst.

  rewrite /actionDeterm.
  move=> s x y; move/imsetP; elim; intros; subst.
  move/imsetP: H1; elim; intros; subst.
  destruct s.
  rewrite /enabled.
  simpl.
  caseOn (s == x0); caseOn (s == x); intros Hx0 Hx.
  rewrite -(eqP Hx0) (eqP Hx) eq_refl //= in H2.
  rewrite Hx (negbTE Hx0); done.
  rewrite (negbTE Hx) Hx0; done.
  rewrite (negbTE Hx) (negbTE Hx0); done.
  rewrite /enabled; done.

  rewrite /RndTH in_set; move/eqP; intro; subst; rewrite /actionDeterm.
  intro.
  move=> x y; rewrite !in_set; move/eqP; intro; subst; move/eqP; intro; subst; done.
  rewrite /RndI.
  move=> s x; rewrite in_set0; done.
  intros; destruct x.
  apply/setUP; right.
  apply/bigcupP; eexists.
  rewrite in_set //=.
  rewrite in_set //=.

  apply/setUP; left; apply/setUP; right.
  apply/bigcupP; eexists.
  rewrite in_set //=.
  apply/imsetP; eexists; rewrite //=.
  destruct s.
  rewrite /enabled //= in H.
  rewrite /enabled //= in H.
Defined.


Definition RndChoose : Task RndPIOA.
  econstructor.
  instantiate (1 := [set Choose]).
  simpl.
  apply/setUP; right; rewrite /RndTH.
  rewrite in_set.
  done.
Defined.

Definition RndOutput : Task RndPIOA.
  econstructor.
  simpl; rewrite /RndTO.
  instantiate (1 := [set Output x | x : A]).
  apply/setUP; left; rewrite in_set; done.
Defined.


Inductive RndSpec (ts : seq (Task RndPIOA)) : Prop:=
  | RndSpec1 : runPIOA _ ts (startTr _) ~~ runPIOA _ nil (startTr _) @ 0 -> RndSpec ts
  | RndSpec2 : (exists n, runPIOA _ ts (startTr _) ~~ runPIOA _ (RndChoose :: nseq n RndOutput) (startTr _) @ 0 )  -> RndSpec ts.

Lemma rndChooseOutput : forall n, runPIOA RndPIOA (RndChoose :: nseq n RndOutput) (startTr _) ~~
                               (x <- D1; ret (Some x, nseq n (Output x))) @ 0 .
  induction n0.
  simpl; rewrite /appTask /startTr; dsimp.
  case:pickP => x.
  move/andP => [i1 i2]; rewrite in_set in i1; rewrite (eqP i1).
  rewrite /external //= set0U.
  dsimp.
  apply measBind_cong_r; intros; dsimp.
  dsimp. 
  case: bigcupP.
  elim=>i; rewrite in_set; move/eqP; intro; subst; case: imsetP.
  elim; done.
  done.
  intro; reflexivity.
  done.
          
  move/andP: (x Choose); elim.
  rewrite in_set /enabled //=.

  simpl.
  rewrite runPIOA_appTask_nseq.
  rewrite (appTask_cong RndPIOA); last by apply IHn0.

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
  case: setUP.
  intro; reflexivity.
  elim.
  right; apply/bigcupP.

  exists [set Output x | x : A].
  rewrite //= /RndTO in_set //=.
  apply/imsetP; eexists; rewrite //=.
  intro Hneq; rewrite (negbTE Hneq) in y1; done.

  move/andP: (y (Output x)); elim; rewrite /enabled //= eq_refl //=; split.
  apply/imsetP; eexists; rewrite //=.
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
  rewrite //= /RndTO.
  move=>x /andP; elim.
  move/imsetP; elim.
  intros; subst.
  done.
  intros; reflexivity.
  rewrite /startTr; dsubdist.

  apply RndSpec2; exists 0%nat.
  simpl.
  rewrite runPIOA_rcons.
  rewrite /RndTH.
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
  move/andP; elim; rewrite /RndTH in_set; move/eqP; intro; subst.
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
    @refinement _ (RndPIOA HD1) (RndPIOA HD2) (RndInputClosed  _) (RndInputClosed  _) e.
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
    exists (RndChoose HD2 :: nseq x (RndOutput HD2)).
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
*)