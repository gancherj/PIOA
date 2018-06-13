Add LoadPath "~/fcf/src".
Require Import PIOA.
Require Import Meas.
Require Import Expansion.
Require Import FCF.Rat.
Require Import List.
Require Import CpdtTactics.

Lemma expansion_cong {A B : Set} {R : Meas A -> Meas B -> Prop} {d1} {d2} {d3} {d4} :
  expansion R d1 d2 ->
  d1 ~~ d3 ->
  d2 ~~ d4 ->
  expansion R d3 d4.
    intros.
    destruct H.
    exists x.
    destruct H; constructor.
    symmetry in H0; rewrite H0; crush.
    symmetry in H1; rewrite H1; crush.
    crush.
Qed.


Inductive TRAct :=
  | Out : nat -> TRAct.

Inductive RndTask :=
| RndChoose : RndTask
| RndOutput : RndTask.

Definition RndQ := option nat.

Definition RndtrT : RndQ -> RndTask -> option (Meas (RndQ * option TRAct)) :=
  fun s t =>
    match s, t with
    | None, RndChoose => Some (
                             x <- unifNats 10;
                               ret (Some x, None))
    | Some x, RndOutput => Some (ret (Some x, Some (Out x)))
    | _, _ => None
    end.

Print mkPIOA.

Definition Rnd : @PIOA TRAct RndTask := mkPIOA TRAct RndTask RndQ None RndtrT (fun _ _ => None).

Inductive TrapTask :=
| TrapChoose : TrapTask
| TrapCompute : TrapTask
| TrapOutput : TrapTask.

Definition TrapQ := (unit + nat + nat)%type. 


Definition TraptrT (s : TrapQ) (t : TrapTask) : option (Meas (TrapQ * option TRAct)) :=
  match s,t with
  | inl (inl tt), TrapChoose => Some ( x <- unifNats 10; ret (inl (inr x), None))
  | inl (inr x), TrapCompute => Some (ret (inr (Nat.sub 9 x), None))
  | inr x, TrapOutput => Some (ret (inr x, Some (Out x)))
  | _, _ => None
              end.

Definition Trap := mkPIOA TRAct TrapTask TrapQ (inl (inl tt)) TraptrT (fun _ _ => None).

Print SimR.

Definition TRSimR : Meas (RndQ * list TRAct) -> Meas (TrapQ * list TRAct) -> Prop := fun d1 d2 =>
(exists t, (d1 ~~ ret (None, t)) /\ (d2 ~~ ret (inl (inl tt), t))) \/
(exists x t, (d1 ~~ ret (Some (Nat.sub 9 x), t)) /\ (d2 ~~ ret (inl (inr x), t))) \/
(exists x t, (d1 ~~ ret (Some x, t)) /\ (d2 ~~ ret (inr x, t))).

Lemma TRSim: SimR Rnd Trap TRSimR.
  constructor.
  unfold TRSimR.
  simpl.
  left.
  exists nil.
  split; apply measEquiv_refl.
  intros.
  repeat destruct H;
  unfold traceOf; rewrite (meas_fmap_cong H); rewrite (meas_fmap_cong H0); unfold fmap; repeat rewrite bind_ret; simpl; apply measEquiv_refl.

  intro.
  remember T.
  destruct r.

  exists (TrapCompute :: TrapChoose :: nil).
  intros.
  repeat destruct H.
  simpl.
  eapply expansion_cong.
  2: {
    eapply (@appTask_cong _ _ Rnd _).
    symmetry; apply H.
  }
  2: {
    eapply (@appTask_cong _ _ Trap _).
    eapply (@appTask_cong _ _ Trap _).

    symmetry; apply H0.

    }
  eapply expansion_cong.
  2: {
    unfold appTask.
    rewrite bindRet.
    simpl.
    rewrite bindAssoc.
    eapply measBind_cong_r; intros.
    symmetry.
    etransitivity.
    apply bindRet.
    apply measEquiv_refl.
    }
  2: {
    unfold appTask.
    simpl.
    rewrite bindAssoc.
    rewrite bindRet.
    simpl.
    repeat rewrite bindAssoc.
    eapply measBind_cong_r; intros.
    symmetry; etransitivity.
    rewrite bindRet.
    rewrite bindRet.
    simpl.
    apply measEquiv_refl.
    apply measEquiv_refl.
    }
  exists (y <- unifNats 10; ret (ret (Some y, x), ret (inr y, x))).
  constructor.
  rewrite bindAssoc.
  apply measBind_cong_r; intros; rewrite bindRet; simpl; apply measEquiv_refl.
  simpl.
  rewrite bindAssoc.
  admit. (* information theoretic by permutation *)
  simpl.
  intros.
  repeat destruct H1; simpl; unfold TRSimR; right; right.
  exists 0%nat, x; split; apply measEquiv_refl.
  exists 1%nat, x; split; apply measEquiv_refl.
  exists 2%nat, x; split; apply measEquiv_refl.
  exists 3%nat, x; split; apply measEquiv_refl.
  exists 4%nat, x; split; apply measEquiv_refl.
  exists 5%nat, x; split; apply measEquiv_refl.
  exists 6%nat, x; split; apply measEquiv_refl.
  exists 7%nat, x; split; apply measEquiv_refl.
  exists 8%nat, x; split; apply measEquiv_refl.
  exists 9%nat, x; split; apply measEquiv_refl.

  admit.
  admit.
  exists (TrapOutput :: nil).
  simpl.
  admit.
Admitted.