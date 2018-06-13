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

Record isExpansion {A B : Set} (R : Meas A -> Meas B -> Prop) (d1 : Meas A) (d2 : Meas B)
       (mu : Meas (Meas A * Meas B)) : Prop :=
  {
    leftEquiv : d1 ~~ (p <- mu; fst p);
    rightEquiv : d2 ~~ (p <- mu; snd p);
    RValid : forall p, In p (measSupport mu) -> R (fst p) (snd p)
                                                  }.

Definition expansion {A B : Set} (R : Meas A -> Meas B -> Prop) d1 d2 :=
  exists mu, isExpansion R d1 d2 mu.

Lemma expansion_cong {A B : Set} (R : Meas A -> Meas B -> Prop) d1 d2 d3 d4 :
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


Lemma expansion_bind {A B C : Set} (R : Meas B -> Meas C -> Prop) (mu : Meas A) (f : A -> Meas B) (g : A -> Meas C) :
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
  intros; apply (H _ (or_intror H0)).
  destruct (IHmu H0) as [IHm IHmExp]; clear IHmu H0.
  destruct (H (snd a) (or_introl eq_refl)) as [muA muAExp]; clear H.
  exists (IHm ++ (measScale (fst a) muA)).
  
  destruct IHmExp, muAExp; constructor.
  rewrite measBind_cons; rewrite measBind_app; eapply measEquiv_app_cong.
  crush.

  rewrite <- measScale_bind_l; symmetry; symmetry in leftEquiv1; rewrite (measScale_cong _ _ _ leftEquiv1); unfold measEquiv, integ, measScale, measBind, measJoin, measSum; intros;
  repeat rewrite sumList_concat;
  repeat rewrite Fold.sumList_map;
  simpl;
  rewrite Fold.sumList_cons; rewrite sumList_nil.
  unfold measScale;
  rewrite Fold.sumList_map;
  rewrite <- ratAdd_0_r;
  apply Fold.sumList_body_eq; intros.
  simpl; ring.

  rewrite measBind_cons; rewrite measBind_app; eapply measEquiv_app_cong.
  crush.

  rewrite <- measScale_bind_l; symmetry; symmetry in rightEquiv1; rewrite (measScale_cong _ _ _ rightEquiv1); unfold measEquiv, integ, measScale, measBind, measJoin, measSum; intros;
  repeat rewrite sumList_concat;
  repeat rewrite Fold.sumList_map;
  simpl;
  rewrite Fold.sumList_cons; rewrite sumList_nil.
  unfold measScale;
  rewrite Fold.sumList_map;
  rewrite <- ratAdd_0_r;
  apply Fold.sumList_body_eq; intros.
  simpl; ring.

  intros.
  unfold measScale in H.
  unfold measSupport in H.
  rewrite map_app in H.
  rewrite in_app_iff in H; destruct H.
  apply RValid0; crush.
  apply RValid1.
  rewrite map_map in H.
  simpl in H.
  crush.
Qed.  


Lemma joinDistrib_expansion_compat {A B : Set} (R : Meas A -> Meas B -> Prop) mu1 mu2 mu f g :
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

  
