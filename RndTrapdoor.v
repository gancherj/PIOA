Add LoadPath "~/fcf/src".
Require Import PIOA.
Require Import Meas.
Require Import Expansion.
Require Import FCF.Rat.
Require Import List.
Require Import CpdtTactics.
Require Import Ring.
Require Import FcfLems.
Require Import FCF.Fold.
Require Import Program.
Require Fin.
From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype generic_quotient finset bigop.

Set Implicit Arguments.
Unset Strict Implicit.


Definition unifFin (n : nat) : Meas ('I_n) :=
  map (fun x => (1 // (S n), x)) (ord_enum n).


Section TrapRandDef.
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


Definition RndQ := option ('I_(S n)).


Definition RndTr (x : RndQ) (a : Action) : option (Meas RndQ) :=
  match x, a with
  | None, Choose => Some (x <- unifFin (S n); ret (Some x))
  | Some x, Output y => if x == y then Some (ret (Some x)) else None
  | _, _ => None
              end.

Definition rndpre := mkPrePIOA [finType of Action] _ None RndTr.

Print mkPIOA.

Definition RndH := set1 Choose.
Definition RndI : {set Action} := set0.
SearchAbout (seq _ -> {set _}).
Definition RndO : {set Action} := Output @: 'I_(S n).

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
  rewrite eq_refl; crush.

  apply/negP.
  move=> Hx.
  rewrite (set1P Hx) in H.
  crush.
Qed.

Lemma rnd_taskStructure : TaskStructure rndpre RndO RndH (set1 RndO) (set1 RndH).
constructor.
apply partition_set1.
apply /eqP /set0Pn; exists (Output ord0); apply mem_imset; done.

apply partition_set1.
apply /eqP /set0Pn; exists (Choose); by rewrite in_set.

intro.
rewrite /actionDeterm.
rewrite in_setU.
move/orP; elim.
rewrite in_set.
move/eqP => H; subst.
elim.

intro; apply /orP; right.
apply/cards1P; exists (Output a).
apply /setP; move=> x.
unfold RndO.
repeat rewrite in_set.
destruct x.
rewrite andbF; done.
elim: (eqVneq o a).
intro; subst.
rewrite /enabled /tr //= .
rewrite !eq_refl andbT.
apply mem_imset; done.

rewrite /enabled /tr //= .
intro H.
rewrite eq_sym in H.
rewrite (negbTE H) andbF; symmetry.
apply negbTE.
apply contraT; intros.
apply negbNE in H0.
have H2 := (eqP H0).
injection H2; intro; subst.
rewrite eq_refl in H; done.
rewrite /enabled /tr andbF; done.


apply /orP; left.
rewrite cards_eq0.
apply /eqP /setP; move=> x; rewrite in_set0 in_set /enabled /tr.
destruct x; rewrite //= /RndO ?andbT.
apply negbTE.
apply /negP.
intro H; destruct (imsetP H); crush.
rewrite andbF; done.
rewrite andbF; done.

rewrite in_set.
move/eqP => H; subst.

elim.
intro; apply/orP; left.
rewrite cards_eq0.
unfold RndH.
apply /set0Pn.
elim.
intros.
rewrite in_set in H; move/andP: H; elim.
rewrite in_set; move/eqP=> Heq; subst; rewrite /enabled/ tr; done.

apply/orP; right.
apply/cards1P; exists Choose.
apply/setP; move=> x; rewrite !in_set /enabled /tr; destruct x; done.
Qed.


Definition RndPIOA : @PIOA [finType of Action].
econstructor.
apply rnd_taskStructure.
instantiate (1 := RndI).
rewrite /trivIset /cover.
rewrite /RndI /RndO /RndH.
repeat rewrite bigcup_setU.
repeat rewrite big_setU1 //=.
repeat rewrite big_set0.
repeat rewrite big_set1.
rewrite set0U.
rewrite cards0.
rewrite setU0.
rewrite add0n.
rewrite addn0.
rewrite cardsU.
have : (Output @: 'I_(S n)) :&: [set Choose] = set0.
apply /setP.
move=> x.
apply /setIP.
rewrite in_set0.
apply /andP.
rewrite negb_and.
apply /orP.
destruct x.
left.
apply /negP.
move=> H.
elim (imsetP H).
done.
right; rewrite in_set; done.
right; rewrite in_set; done.

intros.
rewrite x cards0 subn0; done.
rewrite in_set0; done.
rewrite setU0.
rewrite in_set.
apply /negP.
rewrite eq_sym.
intro H; move/eqP: H.
apply /setP.
move=> H.
move: (H Choose).
repeat rewrite in_set.
intro.
symmetry in H0.
rewrite eq_refl in H0.
move/imsetP: H0.
    by elim.


repeat rewrite in_set.
repeat rewrite negb_or.
apply /andP; split.
rewrite eq_sym; apply /set0Pn; exists (Output ord0).
apply /imsetP; exists ord0; done.
apply /andP; split.
rewrite eq_sym.
apply /set0Pn; exists Choose.
    by rewrite in_set.
    by done.

rewrite /RndI.
intros.
rewrite in_set0 in H.
done.

intros.
destruct x.
apply /setUP; right.
apply /setUP; right.
unfold RndH.
by rewrite in_set.
apply /setUP; right.
apply /setUP; left.
rewrite /RndO.
apply /imsetP; exists o; by done.
destruct s; rewrite /tr in H; simpl in H; done.
Qed.










Inductive TRAct :=
  | Out : nat -> TRAct.

Inductive RndTask :=
| RndChoose : RndTask
| RndOutput : RndTask.


Definition RndtrT (n : nat) `{H : StdNat.nz n} : RndQ -> RndTask -> option (Meas (RndQ * option TRAct)) :=
  fun s t =>
    match s, t with
    | None, RndChoose => Some (
                             x <- unifNats n;
                               ret (Some x, None))
    | Some x, RndOutput => Some (ret (Some x, Some (Out x)))
    | _, _ => None
    end.

Print mkPIOA.

Definition Rnd (n : nat) `{H: StdNat.nz n} : @PIOA TRAct RndTask := mkPIOA TRAct RndTask RndQ None (RndtrT n) (fun _ _ => None).

Inductive TrapTask :=
| TrapChoose : TrapTask
| TrapCompute : TrapTask
| TrapOutput : TrapTask.

Definition TrapQ := (unit + nat + nat)%type. 


Definition TraptrT (n : nat) `{H : StdNat.nz n} (s : TrapQ) (t : TrapTask)  : option (Meas (TrapQ * option TRAct)) :=
  match s,t with
  | inl (inl tt), TrapChoose => Some ( x <- unifNats n; ret (inl (inr x), None))
  | inl (inr x), TrapCompute => Some (ret (inr (Nat.sub (Nat.pred n) x), None))
  | inr x, TrapOutput => Some (ret (inr x, Some (Out x)))
  | _, _ => None
              end.

Definition Trap (n : nat) `{H : StdNat.nz n} := mkPIOA TRAct TrapTask TrapQ (inl (inl tt)) (TraptrT n) (fun _ _ => None).

Definition RTSimR (n : nat) : Meas (RndQ * list TRAct) -> Meas (TrapQ * list TRAct) -> Prop := fun d1 d2 =>
(exists t, (d1 ~~ ret (None, t)) /\ (d2 ~~ ret (inl (inl tt), t))) \/
(exists x t, (d1 ~~ ret (Some x, t)) /\ (d2 ~~ ret (inr x, t))).

Inductive TRSimR (n : nat) (d1 : Meas (TrapQ * list TRAct)) (d2 : Meas (RndQ * list TRAct)) : Prop := 
| TRSimR_case1 : (exists t, (d1 ~~ (ret (inl (inl tt), t))) /\ (d2 ~~ (ret (None, t)))) -> TRSimR n d1 d2
| TRSimR_case2 : (exists t x, (x < n) /\
                              (d1 ~~ (ret (inl (inr (Nat.pred n - x)), t))) /\
                              (d2 ~~ (ret (Some (x), t)))) -> TRSimR n d1 d2
| TRSimR_case3 : (exists t x, (x < n) /\ (d1 ~~ (ret (inr x, t))) /\ (d2 ~~ (ret (Some x, t)))) -> TRSimR n d1 d2.

Lemma unifNats_sub_equal_rev (n : nat) :
  rev (unifNats n) = map (fun p => (fst p, Nat.sub (Nat.pred n) (snd p))) (unifNats n).

  induction n.
  crush.
  simpl.
  unfold unifNats.
  simpl.
  rewrite unif_app.
  rewrite <- map_rev.
  rewrite rev_app_distr.
  fold (@unifNats n).
  rewrite IHn.
  simpl.
  repeat rewrite map_map; simpl.
  repeat rewrite map_app; simpl.
  rewrite PeanoNat.Nat.sub_diag.
  SearchAbout (Nat.pred _ - _).
  generalize (1 // length (allNatsLt n ++ [n])); intros.
  clear IHn.
  assert ([(r,0%nat)] = map (fun x => (r, n - snd x)) ([(r, n)])).
  simpl; rewrite PeanoNat.Nat.sub_diag; crush.
  rewrite H.
  rewrite <- map_app.
  admit.
Admitted.

Lemma unifNats_sub_equiv (n : nat) :
  unifNats n ~~ (x <- unifNats n; ret ((Nat.pred n) - x)).
  admit.
Admitted.

Lemma gt_irrel (n : nat) (H1 H2 : n > 0) : H1 = H2.
  induction n.
  inversion H1.
  
  dependent destruction H1; dependent destruction H2.
  crush.
  crush.
  crush.
  assert (H1 = H2).
  apply IHn.
  crush.
Qed.

Lemma nz_irrel (n : nat) (H1 H2 : StdNat.nz n) : H1 = H2.
  destruct H1, H2.
  rewrite (gt_irrel n agz agz0).
  crush.
Qed.


(*
Lemma rat_red (r : Rat) :
  r == (match r with | RatIntro n (exist _ p _) => let g := Nat.gcd n p in RatIntro (Nat.div n g) (exist _ (Nat.div p g) _) end).
*)

Lemma RTSim (n : nat) `{H : StdNat.nz n} : SimR (Rnd n) (Trap n) (RTSimR n).
  constructor.
  unfold RTSimR.
  left; exists nil; split; apply measEquiv_refl.
  intros.
  repeat destruct H0;
  unfold traceOf; rewrite (meas_fmap_cong H0); rewrite (meas_fmap_cong H1); unfold fmap; repeat rewrite bind_ret; simpl; apply measEquiv_refl.

  intros.
  remember T.
  destruct r.
  exists (TrapCompute :: TrapChoose :: nil).
  intros.
  repeat destruct H1.
  eexists (x0 <- unifNats n; ret (ret _, ret _)).
  simpl.
  constructor.
  rewrite (appTask_cong (Rnd n) _ _ H1).
  unfold appTask; dsimp.
  rewrite (measBind_cong_l (unifNats_sub_equiv n)); dsimp.
  apply measBind_cong_r; intros; dsimp.
  apply measEquiv_refl.
  rewrite (appTask_cong (Trap n) _ _ (appTask_cong (Trap n) _ _ H2)).
  unfold appTask; dsimp.
  apply measBind_cong_r; intros; dsimp.
  apply measEquiv_refl.
  intros.
  apply measBind_in in H3; destruct H3.
  simpl in H3; crush.
  right.
  eexists; eexists; split; apply measEquiv_refl.


  exists (ret (d1, d2)).
  constructor; unfold runPIOA, appTask; simpl.
  rewrite (measBind_cong_l H1); dsimp; crush.
  dsimp; rewrite (measBind_cong_l H2); dsimp; crush.
  intros.
  crush.
  right.
  eexists; eexists; split; crush; apply measEquiv_refl.

  exists (TrapOutput :: nil).
  intros.
  repeat destruct H1.
  exists (ret (d1, d2)).
  constructor.
  unfold appTask.
  rewrite (measBind_cong_l H1); dsimp; crush.
  simpl; unfold appTask; rewrite (measBind_cong_l H2); dsimp; crush.
  intros.
  left.
  crush.
  eexists; crush; apply measEquiv_refl.
  eexists (ret (_, _)).
  constructor.
  unfold appTask.
  rewrite (measBind_cong_l H1); dsimp.
  apply measEquiv_refl.
  simpl.
  unfold appTask.
  rewrite (measBind_cong_l H2); dsimp.
  apply measEquiv_refl.
  simpl.
  right.
  eexists _, _; crush.
  apply measEquiv_refl.
  apply measEquiv_refl.
Qed.

Lemma doub_neg_nat (n : nat) (x : nat) : x < n -> (Nat.pred n - (Nat.pred n - x)) = x.
  induction n; crush.
Qed.

Definition EM (P : Prop) := P \/ ~P.

Definition choose_compute_happened (ts : list TrapTask) := exists a b c,
    ts = a ++ [TrapChoose] ++ b ++ [TrapCompute] ++ c.

Lemma choose_compute_happened_EM : forall ts, EM (choose_compute_happened ts).
  admit.
Admitted.

Lemma TRSim (n : nat) `{H : StdNat.nz n} : SimR (Trap n) (Rnd n) (TRSimR n).
  constructor.
  simpl.
  apply TRSimR_case1.
  eexists; crush; apply measEquiv_refl.
  intros; unfold traceOf. 
  destruct H0; crush.
  unfold fmap; rewrite (measBind_cong_l H1); rewrite (measBind_cong_l H2); dsimp.
  unfold fmap; rewrite (measBind_cong_l H0); rewrite (measBind_cong_l H3); dsimp.
  unfold fmap; rewrite (measBind_cong_l H0); rewrite (measBind_cong_l H3); dsimp.

  intros.
  remember T as r; destruct r.
  exists (RndChoose :: nil).
  intros.

  (* Choose case *)
  destruct H1; crush.
  (* If both are at case 1 *)
  eexists (y <- unifNats n; ret (_, _)); constructor; unfold runPIOA, appTask; simpl.
  rewrite (measBind_cong_l H2); dsimp; crush.
  rewrite (measBind_cong_l (unifNats_sub_equiv n)); dsimp.
  apply measBind_cong_r; intros; dsimp.
  apply measEquiv_refl.

  rewrite (measBind_cong_l H3); dsimp; crush.
  apply measBind_cong_r; intros; dsimp.
  apply measEquiv_refl.
  intros.
  apply TRSimR_case2.
  apply measBind_in in H1; crush.
  eexists; exists x0; crush.
  apply unifNats_in in H4; crush.
  apply measEquiv_refl.
  apply measEquiv_refl.

  (* Cases 2 and 3 are trivial *)

  exists (ret (d1, d2)); constructor; unfold runPIOA, appTask; simpl.
  rewrite (measBind_cong_l H1); dsimp; crush.
  rewrite (measBind_cong_l H4); dsimp; crush.
  intros; apply TRSimR_case2.
  destruct H3.
  eexists; eexists.
  split.
  apply H2.
  crush.
  apply measEquiv_refl.
  apply measEquiv_refl.
  crush.
  
  exists (ret (d1, d2)); constructor; unfold runPIOA, appTask; simpl.
  rewrite (measBind_cong_l H1); dsimp; crush.
  rewrite (measBind_cong_l H4); dsimp; crush.
  intros; crush; apply TRSimR_case3; eexists; eexists; split.
  apply H2.
  split; crush; apply measEquiv_refl.
  

  (* T = Compute *)
  exists nil.
  intros; simpl.
  destruct H1; crush.
  (* case 1 trivial *)
  exists (ret (d1, d2)); constructor; unfold appTask.
  rewrite (measBind_cong_l H2); dsimp; crush.
  dsimp.
  intros; apply TRSimR_case1; eexists; crush; apply measEquiv_refl.

  (* case 2 *)
  eexists (ret (_, _)); constructor; unfold appTask.
  rewrite (measBind_cong_l H1); dsimp.
  apply measEquiv_refl.
  dsimp.
  apply measEquiv_refl.
  intros.
  apply TRSimR_case3.
  exists x.
  exists x0.
  split.
  crush.
  split.
  crush.
  rewrite (doub_neg_nat n x0).
  apply measEquiv_refl.
  crush.
  crush.

  (* case 3 *)
  exists (ret (d1, d2)); constructor; unfold appTask.
  rewrite (measBind_cong_l H1); dsimp; crush.
  dsimp; crush.
  intros; apply TRSimR_case3.
  exists x, x0; crush.

  destruct (choose_compute_happened_EM ts).
  exists (RndOutput :: nil).
  intros.
  destruct H2; crush.
  exists (ret (d1, d2)); constructor; unfold appTask.
  rewrite (measBind_cong_l H3); dsimp; crush.
  rewrite (measBind_cong_l H4); dsimp; crush.
  intros; apply TRSimR_case1; exists x.
  crush.

  (* this case cannot happen, since choose_compute_happened is true *)
  admit.

  eexists (ret (_,_)).
  constructor.
  unfold appTask.
  rewrite (measBind_cong_l H2); dsimp.
  apply measEquiv_refl.
  unfold appTask.
  rewrite (measBind_cong_l H5); dsimp.
  apply measEquiv_refl.
  intros.
  apply TRSimR_case3.
  exists (Out x0 :: x), x0.
  crush; apply measEquiv_refl.

  exists nil.
  intros.
  destruct H2; crush.
  admit. (* same as before *)
  admit. (* easy bc disabled *)
  admit. (* this case is impossible since choose_compute_happened is false *)
Admitted.
