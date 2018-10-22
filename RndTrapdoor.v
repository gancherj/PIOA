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



Definition RndTH := [set [set Choose]].
Definition RndI : {set Action} := set0.
Definition RndTO : {set {set Action}} := [set Output @: 'I_(S n)].

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
  caseOn (o == x0); caseOn (o == x); intros Hx0 Hx.
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
apply/setUP; right; rewrite //= /RndTH.
rewrite in_set //=.
Defined.

Lemma Choose_notin_Out : Choose \notin cover RndTO.
apply/bigcupP.
elim.
move=>x; rewrite //= /RndTO in_set.
move/eqP; intro; subst.
move/imsetP; elim; intros; done.
Qed.

Definition RndOutput : Task RndPIOA.
  econstructor.
instantiate (1 := Output @: 'I_(S n)).
apply/setUP; left; rewrite //= /RndTO .
rewrite in_set //=.
Defined.

Definition Output_in_external1 : forall o, Output o \in external RndPIOA.
rewrite /external.
intro; apply/setUP; right.
apply/bigcupP.
eexists.
rewrite //= /RndTO in_set //=.
apply/imsetP; eexists; rewrite //=.
Qed.

Inductive RndSpec (ts : seq (Task RndPIOA)) : Prop:=
  | RndSpec1 : runPIOA _ ts (startTr _) ~~ runPIOA _ nil (startTr _) @ 0 -> RndSpec ts
  | RndSpec2 : (exists n, runPIOA _ ts (startTr _) ~~ runPIOA _ (RndChoose :: nseq n RndOutput) (startTr _) @ 0 )  -> RndSpec ts.

Lemma rndChooseOutput : forall n, runPIOA RndPIOA (RndChoose :: nseq n RndOutput) (startTr _) ~~
                               (x <- unifFin _; ret (Some x, nseq n (Output x))) @ 0 .
  induction n0.
  simpl; rewrite /appTask /startTr; dsimp.
  case:pickP => x.
  move/andP => [i1 i2]; rewrite in_set in i1; rewrite (eqP i1).
  rewrite /external //= set0U.
  dsimp.
  apply measBind_cong_r; intros; dsimp.
  rewrite (negbTE Choose_notin_Out); reflexivity.
  apply uniford_subdist.
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
  rewrite Output_in_external1.
  reflexivity.
  intro Hneq.
  rewrite (negbTE Hneq) in y1; done.

  move/andP: (y (Output x)); elim; rewrite /enabled //= eq_refl //=; split.
  apply/imsetP; eexists; rewrite //=.
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
destruct s; simpl.
try ltac:(intro Heq; injection Heq; intros; subst); dsubdist; [ apply uniford_subdist | intros; dsubdist ]; try congruence.
congruence.
destruct s; simpl; try congruence.
destruct s; simpl; try congruence.
intro Heq; injection Heq; intros; subst.
dsubdist.
simpl; congruence.
simpl.
destruct (o == o0); simpl.
intro Heq; injection Heq; intro; subst; dsubdist.
congruence.
simpl; congruence.
Qed.

Definition trappre := mkPrePIOA [finType of Action n] [finType of TrapQ] (inl (inl tt)) TrapTr TrapTr_subdist.


Definition TrapTH := [set [set Choose n]; [set Compute n]].
Definition TrapI : {set Action n} := set0.
Definition TrapTO : {set {set Action n}} := [set (@Output n) @: 'I_(S n)].




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

Definition TrapPIOA : @PIOA [finType of (Action n)].
  econstructor.
  instantiate (1 := TrapTH).
  instantiate (1 := TrapTO).
  instantiate (1 := TrapI); constructor.
  rewrite /TrapI; intros; apply/disjointP => y; rewrite in_set //=.
  rewrite /TrapI; intros; apply/disjointP => x; rewrite in_set //=.
  move=> x y; rewrite /TrapTO /TrapTH !in_set.
  move/eqP; intro; subst; move/orP; elim; move/eqP; intros; subst. 
  apply/disjointP; move => z /imsetP; elim; rewrite in_set; intros; subst; done.
  apply/disjointP; move => z /imsetP; elim; rewrite in_set; intros; subst; done.

  move=> x y; rewrite /TrapTO.
  rewrite !in_set; move/eqP => eqx /eqP => eqy; subst.
  rewrite eq_refl; done.

  move=> x y; rewrite /TrapTH.
  rewrite !in_set.
  move/orP; elim; move/eqP; intro; subst;
  move/orP; elim; move/eqP; intro; subst.
  rewrite eq_refl //=.
  intro; apply/disjointP; move=> z; rewrite !in_set; move/eqP; intro; subst; done.
  intro; apply/disjointP; move=> z; rewrite !in_set; move/eqP; intro; subst; done.
  rewrite eq_refl //=.

  instantiate (1 := trappre).
  move=> t /setUP; elim.
  rewrite /TrapTO in_set; move/eqP; intro; subst.
  rewrite /actionDeterm.
  move=> s x y /imsetP; elim => x0 Hx0 Heq; subst; move/imsetP; elim; intros; subst.
  rewrite /enabled //= /TrapTr //=.
  destruct s.
  destruct s; done.
  caseOn (o == x0); caseOn (o == x); move=> Hex0 Hex.
  rewrite -(eqP Hex0) -(eqP Hex) eq_refl in H2; done.
  rewrite Hex (negbTE Hex0); done.
  rewrite Hex0 (negbTE Hex); done.
  rewrite (negbTE Hex0) (negbTE Hex); done.

  rewrite /TrapTH in_set.
  move/orP; elim; rewrite !in_set; move/eqP; intro; subst.
  move=> s x y; rewrite !in_set.
  move/eqP; intro; subst; move/eqP; intro; subst; done.
  move=> s x y; rewrite !in_set.
  move/eqP; intro; subst; move/eqP; intro; subst; done.
  move=> s x; rewrite in_set0; done.
  intros; destruct x.
  apply/setUP; right.
  apply/bigcupP.
  eexists.
  rewrite /TrapTH !in_set.
  apply/orP; left; rewrite //=.
  rewrite in_set //=.
  apply/setUP; left; apply/setUP; right.
  apply/bigcupP; eexists.
  rewrite /TrapTO in_set //=.
  apply/imsetP; eexists; rewrite //=.
  apply/setUP; right; apply/bigcupP; eexists.
  apply/setUP; right; rewrite in_set //=.
  rewrite in_set //=.
Defined.



Definition TrapChoose : Task TrapPIOA.
  econstructor; apply/setUP; right; apply/setUP; left; rewrite in_set; done.
Defined.

Definition TrapCompute : Task TrapPIOA.
  econstructor; apply/setUP; right; apply/setUP; right; rewrite in_set; done.
Defined.

Definition TrapOutput : Task TrapPIOA.
  econstructor; apply/setUP; left; rewrite /RndTO //=; rewrite in_set; done.
Defined.

(* TODO finish *)

Inductive TrapSpec (ts : seq (Task TrapPIOA)) : Prop :=
| TrapSpec1 : runPIOA _ ts (startTr _) ~~ startTr _ @ 0 -> TrapSpec ts
| TrapSpec2 : runPIOA _ ts (startTr _) ~~ (runPIOA _ (TrapChoose :: nil) (startTr _)) @ 0 -> TrapSpec ts
| TrapSpec3 : (exists n, runPIOA _ ts (startTr _) ~~ (runPIOA _ (TrapChoose :: TrapCompute :: nseq n TrapOutput) (startTr _)) @ 0 ) -> TrapSpec ts.

Lemma trapChoose : runPIOA _ (TrapChoose :: nil) (startTr _) ~~
                   (x <- unifFin _; ret (inl (inr x), nil)) @ 0.
  simpl.
  rewrite /appTask /startTr; dsimp.
  case:pickP => y.
  move/andP.
  rewrite in_set; elim; move/eqP => Heq Henab; subst.
  dsimp.
  apply measBind_cong_r; intros; dsimp.
  rewrite /external //= /TrapI /TrapTO set0U.
  case:bigcupP.
  elim; intros.
  rewrite in_set in H1; rewrite (eqP H1) in H2.
  move/imsetP: H2; elim; done.
  reflexivity.
  apply uniford_subdist.
  move: ((y (Choose n))).
  move/negP; elim.
  rewrite /enabled in_set eq_refl //=.
Qed.


Lemma trapChooseComputeOutput : forall n, 
    (runPIOA _ (TrapChoose :: TrapCompute :: nseq n TrapOutput) (startTr _)) ~~
    (x <- unifFin _; ret (inr (f x), nseq n (Output (f x)))) @ 0.                                                                                
  intros; simpl.
  rewrite (runPIOA_cong _ _ _ _ (appTask_cong _ _ _ _ trapChoose)).
  induction n0.
  simpl.
  rewrite /appTask; dsimp.
  apply measBind_cong_r; intros; dsimp.
  case: pickP => y.
  move/andP; elim; rewrite in_set; move/eqP; intro; subst.
  rewrite /external //= set0U.

  case: bigcupP.
  elim; rewrite /TrapTO; intro z; rewrite in_set; move/eqP; intro; subst.
  case:imsetP.
  elim.
  intros; done.
  done.
  intros;
  dsimp.
  reflexivity.

  move: (y (Compute n)).
  move/negP; elim; apply/andP; split.
  rewrite in_set //=.
  rewrite /enabled //=.
  apply uniford_subdist.
  rewrite nseq_rcons.
  rewrite runPIOA_rcons.
  rewrite (appTask_cong _ _ _ _ IHn0).
  rewrite /appTask; dsimp.
  apply measBind_cong_r; intros.
  dsimp.
  case:pickP; intros.
  move/andP: i => [i1 i2].
  rewrite /RndTO in i1.
  move/imsetP: i1; elim; intros; subst.
  case (eqVneq (f x) x1).
  intro; subst; rewrite eq_refl; dsimp.
  rewrite /external //= set0U.
  case: bigcupP; elim; intros.
  reflexivity.
  rewrite /TrapTO.
  exists ([set Output x | x : 'I_(S n)]).
  rewrite in_set //=.
  apply/imsetP; eexists; rewrite //=.
  intro Hneq; rewrite /enabled //= in i2.
  rewrite (negbTE Hneq) in i2; done.
  move: (e (Output (f x))). 
  move/negP; elim; apply/andP.
  rewrite /enabled //= eq_refl //=.
  split; [apply/imsetP; eexists; rewrite //= | done].
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
  rewrite /RndTO.
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
  exists 0%nat. rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ trapChoose).
  symmetry; rewrite trapChooseComputeOutput; symmetry.
  rewrite /appTask; dsimp.
  apply measBind_cong_r; intros; dsimp.


  case:pickP => y.
  move/andP; rewrite in_set; elim; move/eqP; intros; subst; dsimp.

  rewrite /external //= /TrapI /TrapTO set0U.

  case: bigcupP.
  elim => i0; rewrite in_set; move/eqP; intro; subst; case:imsetP.
  elim; done.
  done.
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
  destruct H0.
  apply TrapSpec3.
  rewrite runPIOA_rcons.
  eexists.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ (trapChooseComputeOutput _)).
  symmetry; rewrite trapChooseComputeOutput; symmetry.
  rewrite /appTask.
  dsimp.
  apply measBind_cong_r; intros; dsimp. case:pickP => y.
  move/andP; rewrite /RndTO; elim; move/imsetP; elim; intros; subst.
  have: (f x0) == x1.
  rewrite /enabled in H4.
  simpl in H4.
  apply/contraT.
  intro He; rewrite (negbTE He) in H4; done.
  intro He; rewrite He.
  dsimp.
  rewrite /external //= /TrapI /TrapTO set0U.
  case:bigcupP.
  instantiate (1 := S x).
  elim; intros; simpl.
  rewrite (eqP He).
  reflexivity.
  elim.
  exists ([set Output x | x : 'I_(S n)]).
  rewrite in_set //=.
  apply/imsetP; eexists; rewrite //=.
  move: (y (Output (f x0))).
  move/negP.
  elim.
  apply/andP; split.
  apply/imsetP; eexists; done.
  rewrite /enabled //= eq_refl //=;  done.
  apply uniford_subdist.
  intro; apply TrapSpec3.
  rewrite runPIOA_rcons.
  destruct H0.
  exists x0.
  rewrite (appTask_cong _ _ _ _ H0).
  rewrite (appTask_cong _ _ _ _ (trapChooseComputeOutput _)).
  symmetry; rewrite (trapChooseComputeOutput _); symmetry.
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
  rewrite /external //= /TrapI /TrapTO set0U.
  case:bigcupP.
  elim => i; rewrite in_set; move/eqP; intro; subst; case:imsetP.
  elim; done.
  done.
  intro; dsimp.
  intro; dsimp.


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
*)