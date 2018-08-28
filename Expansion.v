From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
Require Import Posrat.
Require Import Meas.


(* expansion R is the smallest relation that contains R and is closed under convex combinations and is a congruence with respect to ~~. *)


Record isExpansion {A B : eqType} (R : Meas A -> Meas B -> Prop) (d1 : Meas A) (d2 : Meas B)
       (mu : Meas ([eqType of Meas A * Meas B])%type) : Prop :=
  {
    leftEquiv : d1 ~~ (p <- mu; fst p) @ 0;
    rightEquiv : d2 ~~ (p <- mu; snd p) @ 0;
    RValid : forall p,  p \in (measSupport mu) -> R (fst p) (snd p)
                                                  }.

Definition expansion {A B : eqType} (R : Meas A -> Meas B -> Prop) d1 d2 :=
  exists mu, isExpansion R d1 d2 mu.

Lemma expansion_cong {A B : eqType} (R : Meas A -> Meas B -> Prop) d1 d2 d3 d4 :
  d1 ~~ d3 @ 0 ->
  d2 ~~ d4 @ 0 ->
  expansion R d1 d2 ->
  expansion R d3 d4.
  intros.
  destruct H1.
  exists x.
  destruct H1; constructor.
  apply measEquiv_symm in H.
  drewr H.
  done.

  apply measEquiv_symm in H0; drewr H0.
  done.
  done.
Qed.

Definition compSubdist {A B : eqType} (f : A -> Meas B) := (forall x, measMass (f x) <= 1).

Lemma expansion_bind {A B C : eqType} (R : Meas B -> Meas C -> Prop) (mu : Meas A) (f : A -> Meas B) (g : A -> Meas C) :
  compSubdist f ->
  compSubdist g ->
  (forall p, p \in (measSupport mu) -> expansion R (f p) (g p)) ->
  expansion R (p <- mu; f p) (p <- mu; g p).
  intros.
  induction mu; intros.
  exists nil.
  constructor.
  apply measEquiv_refl.
  apply measEquiv_refl.
  done.
  assert (forall p, p \in (measSupport mu) -> expansion R (f p) (g p)).
  intros; apply H1.
  unfold measSupport in *.
  move/mapP: H2; elim; intros.
  apply/mapP. exists x.
  simpl.
  destruct (a.1 != 0).
  rewrite in_cons H2 orbT; done.
  done.
  done.

  destruct (IHmu H2) as [IHm IHmExp]; clear IHmu H2.
  destruct (eqVneq a.1 0).
  eapply expansion_cong.
  eapply measBind_cong_l.
  apply measEquiv_zero_cons.
  rewrite e; done.
  done.
  eapply measBind_cong_l.
  apply measEquiv_zero_cons; rewrite e; done.
  done.


  exists IHm; done.

  assert ((snd a) \in (measSupport (a :: mu))).
  unfold measSupport.
  apply/mapP.
  exists a.
  simpl.
  rewrite (negbTE i); simpl.
  rewrite in_cons eq_refl; done.
  done.
  
  destruct (H1 (snd a) H2) as [muA muAExp]; clear H.

  exists ((measScale (fst a) muA) ++ IHm).
  
  destruct IHmExp, muAExp; constructor.
  eapply measEquiv_0_trans.
  apply measBind_cons.
  apply measEquiv_symm.
  eapply measEquiv_0_trans.
  apply measBind_app.
  apply measEquiv_app_cong_0.

  unfold measEquiv; intros; 
  repeat rewrite integ_measScale.
  rewrite integ_measBind.
  rewrite integ_measScale.
  rewrite pdist_mul_l.
  apply measEquiv_symm in leftEquiv1.
  have Hl := (leftEquiv1 f0 H).
  rewrite ple_le0 in Hl.
  rewrite integ_measBind in Hl.
  rewrite (eqP Hl).
  rewrite pmulr0; done.
  apply measEquiv_symm; apply leftEquiv0.
  eapply measEquiv_0_trans. apply measBind_cons.
  apply measEquiv_symm.
  eapply measEquiv_0_trans. apply measBind_app.
  apply measEquiv_app_cong_0.
  intro; intro.
  rewrite pdist_le0.

  rewrite integ_measBind !integ_measScale -integ_measBind.
  apply/eqP; congr (_ * _).
  symmetry in rightEquiv1.
  have Heq := rightEquiv1 f0 H.
  rewrite pdist_le0 in Heq.
  apply/eqP; done.

  symmetry; done.
  rewrite measSupport_app.
  intro; rewrite mem_cat.
  move/orP; elim.
  intro; apply RValid1.
  rewrite -measSupport_measScale in H.
  done.
  done.
  apply RValid0.
Qed.
  

Definition measCong {A B} (f : Meas A -> Meas B) := forall d1 d2, d1 ~~ d2 @ 0 -> f d1 ~~ (f d2) @ 0.

Definition joinDistrib {A B} (f : Meas A -> Meas B) := forall mu, isSubdist mu -> f (d <- mu; d) ~~ (d <- mu; f d) @ 0.


Lemma joinDistrib_expansion_compat {A B : eqType} (R : Meas A -> Meas B -> Prop) mu1 mu2 mu f g :
  compSubdist f ->
  compSubdist g ->
  isSubdist mu ->
  measCong f ->
  joinDistrib f ->
  measCong g ->
  joinDistrib g ->
  isExpansion R mu1 mu2 mu ->
  mu1 ~~ (p <- (meas_fmap mu fst); p) @ 0 ->
  mu2 ~~ (p <- (meas_fmap mu snd); p) @ 0 ->
  (forall p, p \in (measSupport mu) -> (expansion R) (f (fst p)) (g (snd p)))  ->
  (expansion R) (f mu1) (g mu2).
  intros.
  eapply expansion_cong.
  instantiate (1 := (p <- mu; f (p.1))).
  symmetry; rewrite (H2 _ _ H7).
  rewrite H3.
  rewrite /meas_fmap bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet; reflexivity.
  done.
  apply meas_fmap_isSubdist; done.
  instantiate (1 := (p <- mu; g (p.2))).
  symmetry; rewrite (H4 _ _ H8).
  rewrite H5.
  rewrite /meas_fmap bindAssoc; apply measBind_cong_r; intros.
  rewrite bindRet; reflexivity.
  done.
  by apply meas_fmap_isSubdist.

  apply expansion_bind.
  done.
  done.
  done.
Qed.

Ltac expansion_simp :=
  eapply expansion_cong; [ dsimp; apply measEquiv_refl | dsimp; apply measEquiv_refl | idtac ].

Ltac in_expansion t1 t2 :=
  expansion_simp; eapply expansion_cong; [ t1; apply measEquiv_refl | t2; apply measEquiv_refl | idtac]; expansion_simp.