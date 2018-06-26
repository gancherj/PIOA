Add LoadPath "~/fcf/src".
Add LoadPath ".".
Require Import Meas.
Require Import List.
Require Import CpdtTactics.
Require Import FCF.Rat.
Require Import Program.
Require Import FcfLems.
Require Import Ring.


(* expansion R is the smallest relation that contains R and is closed under convex combinations and is a congruence with respect to ~~. *)


Record isExpansion {A B : Type} (R : Meas A -> Meas B -> Prop) (d1 : Meas A) (d2 : Meas B)
       (mu : Meas (Meas A * Meas B)) : Prop :=
  {
    leftEquiv : d1 ~~ (p <- mu; fst p);
    rightEquiv : d2 ~~ (p <- mu; snd p);
    RValid : forall p, In p (measSupport mu) -> R (fst p) (snd p)
                                                  }.

Definition expansion {A B : Type} (R : Meas A -> Meas B -> Prop) d1 d2 :=
  exists mu, isExpansion R d1 d2 mu.

Lemma expansion_cong {A B : Type} (R : Meas A -> Meas B -> Prop) d1 d2 d3 d4 :
  d1 ~~ d3 ->
  d2 ~~ d4 ->
  expansion R d1 d2 ->
  expansion R d3 d4.
  intros.
  destruct H1.
  exists x.
  destruct H1; constructor.
  symmetry in H; rewrite H; crush.
  symmetry in H0; rewrite H0; crush.
  crush.
Qed.


Lemma expansion_bind {A B C : Type} (R : Meas B -> Meas C -> Prop) (mu : Meas A) (f : A -> Meas B) (g : A -> Meas C) :
  (forall p, In p (measSupport mu) -> expansion R (f p) (g p)) ->
  expansion R (p <- mu; f p) (p <- mu; g p).
  intros.
  induction mu; intros.
  exists [].
  constructor.
  apply measEquiv_refl.
  apply measEquiv_refl.
  crush.
  assert (forall p, In p (measSupport mu) -> expansion R (f p) (g p)).
  intros; apply H.
  unfold measSupport in *.
  apply in_map_iff in H0; repeat destruct H0.
  apply in_map_iff; exists x.
  crush.
  destruct (negb (beqRat (fst a) 0)).
  crush.
  crush.

  destruct (IHmu H0) as [IHm IHmExp]; clear IHmu H0.
  remember (beqRat (fst a) 0) as b; destruct b.
  assert ((fst a) == 0). unfold eqRat; crush.
  clear Heqb.
  eapply expansion_cong.
  eapply measBind_cong_l.
  apply measEquiv_zero_cons.
  crush.
  eapply measBind_cong_l.
  apply measEquiv_zero_cons; crush.
  exists IHm; crush.

  assert (In (snd a) (measSupport (a :: mu))).
  unfold measSupport.
  apply in_map_iff; exists a; crush.
  rewrite <- Heqb.
  crush.
  
  destruct (H (snd a) H0) as [muA muAExp]; clear H.

  exists ((measScale (fst a) muA) ++ IHm).
  
  destruct IHmExp, muAExp; constructor.
  rewrite measBind_cons; rewrite measBind_app; eapply measEquiv_app_cong.
  unfold measEquiv; intros; 
  repeat rewrite integ_measScale.
  rewrite (leftEquiv1 f0).
  repeat rewrite integ_measBind.
  repeat rewrite integ_measScale.
  crush.
  crush.
  rewrite measBind_cons.
  rewrite measBind_app.
  apply measEquiv_app_cong.
  rewrite <- measScale_bind_l.
  apply measScale_cong.
  crush.
  crush.
  intros.
  rewrite measSupport_app in H.
  apply in_app_iff in H; destruct H.
  erewrite <- measSupport_measScale in H.
  crush.
  intro.
  rewrite H1 in Heqb; crush.
  crush.
Qed.


Definition fmap {A B} (d : Meas A) (f : A -> B) : Meas B :=
  (x <- d; ret (f x)).

Definition measCong {A B} (f : Meas A -> Meas B) := forall d1 d2, d1 ~~ d2 -> f d1 ~~ f d2.

Definition joinDistrib {A B} (f : Meas A -> Meas B) := forall mu, f (d <- mu; d) ~~ (d <- mu; f d).


Lemma joinDistrib_expansion_compat {A B : Type} (R : Meas A -> Meas B -> Prop) mu1 mu2 mu f g :
  measCong f ->
  joinDistrib f ->
  measCong g ->
  joinDistrib g ->
  isExpansion R mu1 mu2 mu ->
  mu1 ~~ (p <- (fmap mu fst); p) ->
  mu2 ~~ (p <- (fmap mu snd); p) ->
  (forall p, In p (measSupport mu) -> (expansion R) (f (fst p)) (g (snd p)))  ->
  (expansion R) (f mu1) (g mu2).
  
intros.
eapply expansion_cong.

instantiate (1 := (p <- mu; f (fst p))).
symmetry.
rewrite (H _ _ H4).
rewrite (H0 _).
unfold fmap.
repeat rewrite bindAssoc.
apply measBind_cong_r; intros; repeat rewrite bindRet; simpl; apply measEquiv_refl.

instantiate (1 := (p <- mu; g (snd p))).
symmetry; rewrite (H1 _ _ H5).
rewrite (H2 _).
unfold fmap.
repeat rewrite bindAssoc.
apply measBind_cong_r; intros; repeat rewrite bindRet; simpl; apply measEquiv_refl.

apply expansion_bind.
intros.
crush.
Qed.

Ltac expansion_simp :=
  eapply expansion_cong; [ dsimp; apply measEquiv_refl | dsimp; apply measEquiv_refl | idtac ].

Ltac in_expansion t1 t2 :=
  expansion_simp; eapply expansion_cong; [ t1; apply measEquiv_refl | t2; apply measEquiv_refl | idtac]; expansion_simp.