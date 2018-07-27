From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset.
Require Import PIOA Meas Posrat Expansion CpdtTactics.

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
  Context (n : nat).

Inductive Action : Type :=
  | Choose : Action 
  | Output : 'I_(S n) -> Action
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


Definition RndQ := [eqType of option ('I_(S n))].

Lemma uniford_subdist : isSubdist (unifFin [finType of 'I_(S n)]).
  apply isDist_isSubdist; apply unif_isDist; rewrite //= -cardE card_ord; done.
Qed.
  
Definition RndTr (x : RndQ) (a : Action) : option (Meas RndQ) :=
  match x, a with
  | None, Choose => Some (x <- unifFin ([finType of 'I_(S n)]); ret (Some x))
  | Some x, Output y => if x == y then Some (ret (Some x)) else None
  | _, _ => None
              end.

Lemma RndTr_subDist x a m : RndTr x a = Some m -> isSubdist m.
destruct x, a; simpl; try congruence.
case (eqVneq o o0); intro.
subst; rewrite eq_refl.
intro H; injection H; intro; subst.
dsubdist.
rewrite (negbTE i); congruence.
intro H; injection H; intro; subst.
dsubdist.
apply uniford_subdist.
intros; dsubdist.
Qed.


Definition rndpre : prePIOA := mkPrePIOA [finType of Action] [finType of RndQ] None RndTr RndTr_subDist.


Definition RndH := set1 Choose.
Definition RndI : {set Action} := set0.
SearchAbout (seq _ -> {set _}).
Definition RndO : {set Action} := Output @: 'I_(S n).

Lemma rnd_taskStructure : TaskStructure (rndpre) (RndO ) (RndH ) (set1 (RndO )) (set1 (RndH )).

constructor.


apply partition_set1; apply /eqP /set0Pn; exists (Output ord0); apply mem_imset; done.
apply partition_set1; apply /eqP /set0Pn; exists (Choose ); by rewrite in_set.

intros.
rewrite /actionDeterm; intros.

rewrite in_setU in H; move/orP: H => [H | H]; rewrite in_set in H; rewrite (eqP H).
destruct s.
rewrite /enabled.

simpl.
apply/orP; right.
apply/cards1P; exists (Output o); apply setP; move=>x; rewrite !in_set; destruct x; rewrite //=.
rewrite andbF; symmetry; apply/eqP; done.
destruct (eqVneq o o0).
rewrite /RndO.
subst; rewrite !eq_refl andbT.
apply/ imsetP; exists o0; done.
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


have : ((@Output ) @: 'I_(S n)) :&: [set Choose] = set0.

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
apply/eqP/setP; intro H; have HC := H (Output ord0). 
rewrite in_set0 in HC.
symmetry in HC;
move/imsetP: HC.
elim.
exists ord0; done.

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
exists o; done.
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
  instantiate (1 := [set Output x | x : 'I_(S n)]).
  apply/setUP; left; rewrite in_set; done.
Defined.

Check runPIOA.


Inductive RndSpec (ts : seq (Task RndPIOA)) : Prop:=
  | RndSpec1 : runPIOA _ ts (startTr _) ~~ runPIOA _ nil (startTr _) @ 0 -> RndSpec ts
  | RndSpec2 : (exists n, runPIOA _ ts (startTr _) ~~ runPIOA _ (RndChoose :: nseq n RndOutput) (startTr _) @ 0 )  -> RndSpec ts.

Lemma rndChooseOutput : forall n, runPIOA RndPIOA (RndChoose :: nseq n RndOutput) (startTr _) ~~
                               (x <- unifFin _; ret (Some x, nseq n (Output x))) @ 0 .
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
  apply uniford_subdist.
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
  apply uniford_subdist.
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
  apply uniford_subdist.
Qed.

Lemma RndInputClosed : inputClosed RndPIOA.
  constructor.
Qed.


End RandDefs.

Section TrapDefs.
  Context (n : nat).

Definition TrapQ := [eqType of (unit + 'I_(S n) + 'I_(S n))%type]. 

Context (f : 'I_(S n) -> 'I_(S n)).
Hypothesis (H : bijective f).

Definition TrapTr (x : TrapQ) (a : Action n) : option (Meas TrapQ) :=
  match x, a with
  | inl (inl _), Choose => Some (x <- unifFin ([finType of 'I_(S n)]); ret (inl (inr x)))
  | inl (inr x), Compute => Some (ret (inr (f x)))
  | inr x, Output y => if x == y then Some (ret (inr x)) else None
  | _, _ => None
              end.

Lemma TrapTr_subdist x a mu : TrapTr x a = Some mu -> isSubdist mu.
destruct x,a. 
destruct s; crush.
dsubdist; [ apply uniford_subdist | intros; dsubdist ].
destruct s; crush.
destruct s; crush.
dsubdist.
destruct o; crush.
rewrite /TrapTr.
destruct (o == o0); crush; dsubdist.
rewrite /TrapTr; crush.
Qed.

Definition trappre := mkPrePIOA [finType of Action n] [finType of TrapQ] (inl (inl tt)) TrapTr TrapTr_subdist.


Definition TrapH := [set Choose n; Compute n].
Definition TrapI : {set Action n} := set0.
Definition TrapO : {set Action n} := (@Output n) @: 'I_(S n).


Lemma TrapOneqTrapH : TrapO != TrapH.
  rewrite /TrapO /TrapH.
  apply/eqP/setP; move => H2; move: (H2 (Choose n)); rewrite !in_set //=.
  move/imsetP; elim; move=> y; done.
Qed.

Lemma TrapLocal_neq0 : TrapH != set0 /\ TrapO != set0.
  split.
  apply/set0Pn.
  exists (Choose n).
  apply in_set2.
  apply/set0Pn; exists (Output ord0); apply /imsetP; exists ord0; done.
Qed.

Lemma TrapLocal_disjoint : TrapH :&: TrapO = set0.
  apply/setP; move=> x; rewrite in_setI /TrapH /TrapO !in_set.
  elim x; simpl.
  apply/imsetP; elim; done.
  done.
  apply/imsetP; elim; done.
Qed.

Lemma set1_inter_neq {A : finType} (x y : A) : x != y -> [set x] :&: [set y] = set0.
  intro;apply/setP.
  move=>a.
  rewrite in_setI !in_set.
  destruct (eqVneq a x); subst.
  rewrite (negbTE H0) andbF; done.
  destruct (eqVneq a y); subst.
  rewrite (negbTE i) andFb; done.
  rewrite (negbTE i) (negbTE i0); done.
Qed.


Lemma trap_taskStructure : TaskStructure trappre TrapO TrapH (set1 (RndO n)) [set (set1 (Choose n)); (set1 (Compute n))].
constructor.
- apply partition_set1; apply/eqP /set0Pn; exists (Output ord0); rewrite /TrapO; by apply mem_imset.
- rewrite /TrapH; apply /andP; split.
  - rewrite /cover. rewrite !bigcup_setU !big_set1; done.
  - apply /andP; split.
    - rewrite /trivIset /cover !bigcup_setU !big_set1 !big_setU1 //=.
      rewrite !big_set1 cardsU. 
      rewrite set1_inter_neq; last first. done.
      rewrite cards0 subn0; done.
      - rewrite in_set; apply/eqP/setP => x; move: (x (Choose n)); rewrite !in_set; done.
      - rewrite in_set negb_or !in_set; apply/andP. split; rewrite eq_sym; rewrite -card_gt0 cards1; done.
- move=>T; rewrite !in_setU => HT; case (or3P HT); rewrite in_set => Teq; rewrite (eqP Teq) /actionDeterm.
  - rewrite /RndO; elim => a. rewrite cards_eq0.
  - apply/orP; left; apply /eqP /setP => x; rewrite !in_set; apply negbTE; elim x.
    - rewrite negb_and; apply /orP; left; apply /negP => Hin; destruct (imsetP Hin); done.
    - intro; rewrite negb_and; apply /orP; right; rewrite /enabled /tr //=; elim a; done.
    - rewrite negb_and; apply /orP; left; apply /negP => Hin; destruct (imsetP Hin); done.
  - apply/orP; right; apply /cards1P; exists (Output a); apply /setP => x; elim x.
    - rewrite !in_set; apply negbTE; rewrite negb_and; apply /orP; left; apply /imsetP => x0; elim x0; done.
    - move=> o; rewrite !in_set /enabled /tr //=; elim (eqVneq o a) => Heq; subst.
      - rewrite !eq_refl andbT; apply /imsetP; exists a; done.
      - rewrite eq_sym; rewrite (negbTE Heq) andbF; symmetry; move/eqP: Heq => Heq; apply /negbTE /negP; move/eqP; intro Hneq; injection Hneq; congruence.
      - rewrite !in_set /enabled /tr //= andbF; done.
    - elim => a; destruct a; apply /orP; rewrite /enabled /tr //=.
        - right.
         - apply /cards1P; exists (Choose n). apply /setP. elim. rewrite ?in_set; done.
        - move=> o; rewrite !in_set; done.
        - rewrite !in_set; done.
    - left; apply contraT => Hin; rewrite cards_eq0 in Hin; move/set0Pn: Hin; elim => y; rewrite !in_set; elim y; done.
    - left; apply contraT => Hin; rewrite cards_eq0 in Hin; move/set0Pn: Hin; elim => y; rewrite !in_set; elim y; done.
        
  - elim.
    - elim => s; apply /orP.
    - left; apply contraT => Hin; rewrite cards_eq0 in Hin; move/set0Pn: Hin; elim => y; rewrite !in_set; elim y; done.
    - right; apply /cards1P; exists (Compute n); apply /setP; elim.
      - by rewrite !in_set. 
      - intro; by rewrite !in_set. 
      - by rewrite !in_set /enabled /tr.
    - intro; apply/orP; left; apply contraT => Hin; rewrite cards_eq0 in Hin; move/set0Pn: Hin; elim => y; rewrite !in_set; elim y; done.
Qed.

Definition TrapPIOA : @PIOA [finType of (Action n)].
econstructor.
apply trap_taskStructure.
instantiate (1 := TrapI).
rewrite /trivIset /cover !big_setU1 //= /TrapI. rewrite !big_set0 setU0 addn0 set0U cards0 add0n !cardsU.
rewrite set1_inter_neq; last first. done.
rewrite setIC TrapLocal_disjoint !cards0 !subn0; done.
by rewrite in_set0.

rewrite in_setU1 negb_or; apply /andP; split.
apply /contraT; rewrite negbK; move=>Heq. 
move/eqP/setP: Heq => Heqi; move: (Heqi (Choose n)); rewrite /TrapO /TrapH !in_set //=.
move/imsetP; elim; move=> x; done.
by rewrite in_set0.

rewrite !in_setU1 !negb_or.
apply /andP; split.
rewrite eq_sym; apply /set0Pn; exists (Output ord0); apply /imsetP; exists ord0; done.
apply/andP;split.
rewrite eq_sym; apply /set0Pn; exists (Choose n); rewrite !in_set; done.
by rewrite in_set0.
by rewrite in_set0.

rewrite in_setU negb_or; apply/andP; rewrite in_set.
split; [apply TrapOneqTrapH | by rewrite in_set0].
rewrite  setU0 !in_set negb_or; apply /andP; split; rewrite eq_sym; elim (TrapLocal_neq0); done.

move=> s x; rewrite /TrapI in_set0; done.

intros; rewrite /TrapI /TrapO /TrapH set0U !in_setU !in_set; elim x.
apply/orP; right; done.
move=> o; apply/orP; left; apply /imsetP; exists o; done.
apply/orP; right; done.
Defined.

Definition TrapChoose : Task TrapPIOA.
  econstructor; apply/setUP; right; apply/setUP; left; rewrite in_set; done.
Defined.

Definition TrapCompute : Task TrapPIOA.
  econstructor; apply/setUP; right; apply/setUP; right; rewrite in_set; done.
Defined.

Definition TrapOutput : Task TrapPIOA.
  econstructor; apply/setUP; left; rewrite /RndO //=; rewrite in_set; done.
Defined.

Inductive TrapSpec (ts : seq (Task TrapPIOA)) : Prop :=
| TrapSpec1 : runPIOA _ ts (startTr _) ~~ startTr _ @ 0 -> TrapSpec ts
| TrapSpec2 : runPIOA _ ts (startTr _) ~~ (runPIOA _ (TrapChoose :: nil) (startTr _)) @ 0 -> TrapSpec ts
| TrapSpec3 : runPIOA _ ts (startTr _) ~~ (runPIOA _ (TrapChoose :: TrapCompute :: nil) (startTr _)) @ 0 -> TrapSpec ts
| TrapSpec4 : (exists n, runPIOA _ ts (startTr _) ~~ (runPIOA _ (TrapChoose :: TrapCompute :: nseq n TrapOutput) (startTr _)) @ 0 ) -> TrapSpec ts.

Lemma trapChoose : runPIOA _ (TrapChoose :: nil) (startTr _) ~~
                   (x <- unifFin _; ret (inl (inr x), nil)) @ 0.
  simpl.
  rewrite /appTask /startTr; dsimp.
  case:pickP => y.
  move/andP.
  rewrite in_set; elim; move/eqP => Heq Henab; subst.
  dsimp.
  apply measBind_cong_r; intros; dsimp.
  rewrite /external //= /TrapI /TrapO set0U.
  case:imsetP.
  elim; done.
  reflexivity.
  apply uniford_subdist.
  move: ((y (Choose n))).
  move/negP; elim.
  rewrite /enabled in_set eq_refl //=.
Qed.

Lemma trapChooseCompute : (runPIOA _ (TrapChoose :: TrapCompute :: nil) (startTr _)) ~~
                   (x <- unifFin _; ret (inr (f x), nil)) @ 0.
  simpl.
  have He := trapChoose.
  simpl in He.
  rewrite (appTask_cong _ _ _ _ He).
  rewrite /appTask; dsimp; apply measBind_cong_r; intros; dsimp.
  case:pickP => y.
  move/andP; rewrite in_set; elim; move/eqP; intros; subst.
  dsimp.
  rewrite /external //= /TrapI /TrapO set0U.
  case:imsetP.
  elim;done.
  reflexivity.
  move: (y (Compute n)).
  move/negP; elim.
  rewrite /enabled in_set eq_refl //=.
  apply uniford_subdist.
Qed.

Lemma trapChooseComputeOutput : forall n, 
    (runPIOA _ (TrapChoose :: TrapCompute :: nseq n TrapOutput) (startTr _)) ~~
    (x <- unifFin _; ret (inr (f x), nseq n (Output (f x)))) @ 0.                                                                                
  intros; simpl.
  have HC := trapChooseCompute.
  rewrite (runPIOA_cong _ _ _ _ HC).
  clear HC.
  induction n0.
  simpl; reflexivity. 
  rewrite nseq_rcons; rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ IHn0).
  rewrite /appTask; dsimp.
  apply measBind_cong_r; intros; dsimp.
  case: pickP => y.
  move/andP; rewrite /RndO; elim.
  move/imsetP; elim; intros; subst.
  rewrite /enabled in H3.
  simpl in H3.
  case (eqVneq (f x) x0).
  intro; subst.
  rewrite eq_refl.
  dsimp.
  rewrite /external //= /TrapI /TrapO //= set0U.
  case: imsetP.
  reflexivity.
  elim.
  eexists; done.
  move=>Hn; rewrite (negbTE Hn) in H3.
  done.
  move: (y (Output (f x))); move/negP; elim.
  apply/andP; split.
  apply/imsetP; eexists; rewrite //=.
  rewrite /enabled //= eq_refl //=.
  apply uniford_subdist.
Qed.

Lemma trapSpec : forall ts, TrapSpec ts.
  induction ts using last_ind.
  apply TrapSpec1; reflexivity.
  destruct IHts.
  destruct x.
  have Hi := i.
  simpl in Hi.
  move/setUP: Hi.
  rewrite in_set.
  rewrite in_set.
  elim.
  move/eqP.
  rewrite /RndO.
  intro; subst; apply TrapSpec1.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite /appTask /startTr; dsimp.
  case:pickP => y. 
  move/andP; elim; move/imsetP; elim; intros; subst.
  done.
  reflexivity.

  move/orP; elim.
  rewrite in_set; move/eqP; intro; subst.
  apply TrapSpec2.
  simpl.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  reflexivity.
  rewrite in_set; move/eqP; intro; subst.
  apply TrapSpec1.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite /appTask; dsimp; rewrite /startTr; dsimp.
  case:pickP => y.
  move/andP; elim; rewrite in_set; move/eqP; intro; subst.
  reflexivity.
  reflexivity.

  destruct x.
  have Hi := i.
  move/setUP: Hi.
  simpl.
  elim.
  rewrite in_set; move/eqP; intro; subst.
  apply TrapSpec2.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ trapChoose).
  symmetry; rewrite trapChoose; symmetry.
  rewrite /appTask.
  dsimp; apply measBind_cong_r; intros; dsimp.
  case:pickP => y.
  move/andP; elim; move/imsetP; elim; intros; subst.
  reflexivity.
  reflexivity.
  apply uniford_subdist.
  move/setUP; elim.
  rewrite in_set; move/eqP; intro; subst; apply TrapSpec2.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ trapChoose).
  symmetry; rewrite trapChoose; symmetry.
  rewrite /appTask.
  dsimp; apply measBind_cong_r; intros; dsimp.
  case:pickP => y.
  move/andP; rewrite in_set; elim; move/eqP; intros; subst.
  reflexivity.
  reflexivity.
  apply uniford_subdist.
  rewrite in_set; move/eqP; intro; subst.
  apply TrapSpec3.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ trapChoose).
  symmetry; rewrite trapChooseCompute; symmetry.
  rewrite /appTask; dsimp.
  apply measBind_cong_r; intros; dsimp.


  case:pickP => y.
  move/andP; rewrite in_set; elim; move/eqP; intros; subst; dsimp.

  rewrite /external //= /TrapI /TrapO set0U.

  case: imsetP.
  elim; done.
  reflexivity.

  move: (y (Compute n)).
  move/negP.
  elim.
  rewrite /enabled in_set eq_refl //=.
  apply uniford_subdist.


  destruct x.
  have Hi := i.
  move/setUP: Hi.
  simpl.
  elim.
  rewrite in_set; move/eqP; intro; subst.

  apply TrapSpec4.
  exists 1%nat.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ trapChooseCompute).
  symmetry; rewrite trapChooseComputeOutput; symmetry.
  rewrite /appTask.
  dsimp.
  apply measBind_cong_r; intros; dsimp. case:pickP => y.
  move/andP; rewrite /RndO; elim; move/imsetP; elim; intros; subst.
  have: f x == x0.
  rewrite /enabled in H4.
  simpl in H4.
  apply/contraT.
  intro He; rewrite (negbTE He) in H4; done.
  intro He; rewrite He.
  dsimp.
  rewrite /external //= /TrapI /TrapO set0U.
  case:imsetP.
  elim.
  intros.
  injection H5.
  intro; subst.
  rewrite (eqP He).
  reflexivity.
  elim.
  eexists; rewrite //=.
  move: (y (Output (f x))).
  move/negP.
  elim.
  apply/andP; split.
  apply/imsetP; eexists; done.
  rewrite /enabled //= eq_refl //=;  done.
  apply uniford_subdist.
  intro; apply TrapSpec3.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ trapChooseCompute).
  symmetry; rewrite trapChooseCompute; symmetry.
  rewrite /appTask.
  dsimp; apply measBind_cong_r; intros; dsimp.
  case:pickP => y.
  move/andP; elim.
  move/setUP: H1.
  elim;
  rewrite in_set; move/eqP; intro; subst; rewrite in_set; move/eqP; intro; subst.

  done.
  done.
  reflexivity.
  apply uniford_subdist.

  destruct H0.
  destruct x.
  have Hi := i.
  move/setUP: Hi; elim.
  rewrite in_set.
  move/eqP; intro; subst.
  apply TrapSpec4.
  exists (S x0).
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ (trapChooseComputeOutput _)).
  symmetry; rewrite trapChooseComputeOutput; symmetry.
  rewrite /appTask.
  dsimp; apply measBind_cong_r; intros; dsimp.
  case:pickP => y.
  move/andP; elim.
  move/imsetP; elim; intros; subst.
  have: f x = x1.
  rewrite /enabled //= in H4.
  apply/eqP/contraT.
  intro Hq; rewrite (negbTE Hq) in H4; done.
  intro; subst; rewrite eq_refl //=.
  dsimp.
  rewrite /external //= /TrapI /TrapO set0U; case: imsetP.
  elim; intros; subst; reflexivity.
  elim; eexists; done.
  move: (y (Output (f x))).
  move/negP; elim.
  apply/andP; split.
  apply/imsetP; eexists; rewrite //=.
  rewrite /enabled //= eq_refl //=.
  apply uniford_subdist.
  intro; apply TrapSpec4; exists x0.
  symmetry; rewrite trapChooseComputeOutput; symmetry.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ (trapChooseComputeOutput _)).

  rewrite /appTask.
  dsimp; apply measBind_cong_r; intros; dsimp.
  case:pickP => y.
  move/andP; elim.
  rewrite //= in H1.
  move/setUP: H1; elim; rewrite in_set; move/eqP; intro; subst; rewrite in_set; move/eqP; intro; subst.
  done.
  done.
  reflexivity.
  apply uniford_subdist.
Qed.


Lemma trapInputClosed : inputClosed TrapPIOA.
  constructor.
Qed.

End TrapDefs.

Section RndTrapProofs.
  Context (n : nat).
  Context (f : 'I_(S n) -> 'I_(S n)).
  Context (fbij : bijective f).
  
Lemma TRRefine : @refinement _ (TrapPIOA f) (RndPIOA n) (trapInputClosed f) (RndInputClosed _) 0.
  unfold refinement.
  intro.
  destruct (trapSpec ts);
  rewrite /traceOf.
  exists nil.
  simpl.
  rewrite (fmap_cong _ _ _ _ H).
  reflexivity.
  exists nil.
  simpl.
  rewrite (fmap_cong _ _ _ _ H).
  rewrite /meas_fmap.
  simpl.
  rewrite /appTask /startTr.
  dsimp.
  case: pickP.
  intro; move/andP; elim; rewrite in_set; move/eqP; intro; subst; intro.
  dsimp.
  apply measBind_irr.
  apply unif_isDist.
  rewrite -cardE card_ord; done.
  intro; dsimp.
  rewrite /external //= /TrapI /TrapO set0U.
  case:imsetP.
  elim; done.
  intro; dsimp.
  intro; dsimp.

  exists (RndChoose n :: nil).
  rewrite (fmap_cong _ _ _ _ H).
  etransitivity.
  apply fmap_cong.
  apply trapChooseCompute.
  symmetry; etransitivity.
  have H2 := rndChooseOutput 0%nat.
  simpl in H2.
  simpl.
  apply fmap_cong.
  apply H2.
  rewrite /meas_fmap; dsimp; apply measBind_cong_r; intros; dsimp.


  apply uniford_subdist.
  destruct H.
  exists (RndChoose n :: nseq x (RndOutput n)).
  rewrite (fmap_cong _ _ _ _ H).
  rewrite (fmap_cong _ _ _ _ (trapChooseComputeOutput _)).
  symmetry; rewrite (fmap_cong _ _ _ _ (rndChooseOutput _)).
  rewrite /meas_fmap; dsimp.

  rewrite (measBind_cong_l (finType_unif_bij fbij)).
  rewrite /meas_fmap.
  dsimp.

  apply measBind_cong_r; intros; dsimp.
  apply uniford_subdist.
  intro; dsubdist.
  intros; dsubdist.
Qed.


Lemma RTRefine : @refinement _ (RndPIOA n) (TrapPIOA f)  (RndInputClosed _) (trapInputClosed f) 0.
  intro.
  rewrite /traceOf.
  destruct (rndSpec ts).
  exists nil.
  rewrite (fmap_cong _ _ _ _ H).
  reflexivity.
  destruct H.
  exists (TrapChoose f :: TrapCompute f :: nseq x (TrapOutput f)).

  rewrite (fmap_cong _ _ _ _ H).
  rewrite (fmap_cong _ _ _ _ (rndChooseOutput _)).
  rewrite (fmap_cong _ _ _ _ (trapChooseComputeOutput _)).
  rewrite /meas_fmap; dsimp.
  rewrite (measBind_cong_l (finType_unif_bij fbij)) /meas_fmap; dsimp.
  apply measBind_cong_r; intros; dsimp.
  apply uniford_subdist.
  intros; dsubdist; intros; dsubdist.
Qed.

End RndTrapProofs.