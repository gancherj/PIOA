

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems CompPIOAProps.

Definition measFilter {A : eqType} (m : Meas A) (f : A -> bool) :=
  filter (fun p => f p.2) m.

Check integ.

Lemma integ_filter {A : eqType} (m : Meas A) (f : A -> bool) f2 :
  integ (measFilter m f) f2 =
  integ m (fun x => if f x then f2 x else 0).
  induction m.
  simpl.
  rewrite !integ_nil //=.
  simpl.
  rewrite integ_cons.
  caseOn (f a.2); intro He.
  rewrite He.
  rewrite integ_cons.
  rewrite IHm.
  done.
  rewrite (negbTE He).
  rewrite pmulr0 padd0r.
  done.
Qed.

Lemma measSupport_measFilter {A : eqType} (m : Meas A) (f : A -> bool) x :
  x \in measSupport (measFilter m f) -> (x \in measSupport m) && (f x).
  induction m.
  simpl.
  rewrite /measSupport //=.
  simpl.
  caseOn (f a.2).
  intro He; rewrite He.
  rewrite !measSupport_cons.
  caseOn (a.1 == 0).
  intro He2; rewrite He2.
  done.
  intro He2; rewrite (negbTE He2).
  rewrite in_cons.
  move/orP; elim.
  move/eqP; intro; subst.
  rewrite in_cons.
  apply/andP; split.
  rewrite eq_refl orTb; done.
  done.
  intros.
  move/andP: (IHm H).
  elim.
  rewrite in_cons.
  intros.
  rewrite H0 H1.
  rewrite orbT //=.
  intro He; rewrite (negbTE He).
  intro.
  move/andP: (IHm H).
  elim.
  intros.
  rewrite measSupport_cons.
  caseOn (a.1 == 0); intro He2.
  rewrite He2.
  rewrite H0 H1; done.
  rewrite (negbTE He2).
  rewrite in_cons H0 H1 orbT //=. 
Qed.

Lemma measFilter_cong {A : eqType} (m1 m2 : Meas A) (f : A -> bool) :
  m1 ~~ m2 @ 0 -> measFilter m1 f ~~ measFilter m2 f @ 0.
  intros; rewrite /measEquiv; intros.
  rewrite pdist_le0.
  rewrite !integ_filter.
  have: forall x, (fun y => if f y then f0 y else 0) x <= 1.
  intros; caseOn (f x).
  intro He; rewrite He.
  done.
  intro He; rewrite (negbTE He).
  done.
  intros.
  have H2 := H _ x.
  rewrite pdist_le0 in H2.
  done.
Qed.

Lemma filter_subDist {A} (M : Meas A) f :
  isSubdist M -> isSubdist (measFilter M f).
  have: measMass (measFilter M f) <= measMass M.
  rewrite /measMass /measFilter.
  induction M.
  rewrite big_nil; done.
  rewrite big_filter !big_cons.
  caseOn (f a.2).
  intro He; rewrite He.
  apply ple_add_lr.
  apply ple_refl.
  rewrite big_filter in IHM; done.
  intro He; rewrite (negbTE He).
  rewrite -(padd0r (\big[padd/0]_(j <- M | f j.2) j.1)).
  apply ple_add_lr.
  destruct a.
  destruct p; done.
  rewrite big_filter in IHM; done.
  intros.
  rewrite /isSubdist.
  eapply ple_trans.
  apply x.
  done.
Qed.

Lemma measFilter_disj {A} (M : Meas A) f :
  M ~~ (measFilter M f) ++ (measFilter M (fun x => negb (f x))) @ 0.
  rewrite /measEquiv; intros.
  rewrite pdist_le0.
  rewrite /integ.
  rewrite big_cat.
  simpl.
  induction M.
  rewrite //= !big_nil; done.
  rewrite //= !big_cons.
  caseOn (f a.2); intro He; rewrite He //=.
  rewrite big_cons.
  rewrite -paddrA.
  rewrite -(eqP IHM).
  done.
  rewrite (negbTE He).
  rewrite big_cons.
  rewrite paddrA.
  rewrite (paddrC (\big[padd/0]_(i <- measFilter M f) (i.1 * f0 i.2)) (a.1 * f0 a.2)).
  rewrite -paddrA.
  rewrite -(eqP IHM).
  done.
Qed.


Definition pc_pairwise_disj {A : eqType} (l : seq (pred A)) := forall f g x,
    List.In f l -> List.In g l -> ~~ (f x && g x).

Definition pc_complete {A : eqType} (l : seq (pred A)) (g : pred A) := forall x, g x -> exists f,
      List.In f l /\ f x.

(* filtering m by a series of pairwise disjoint predicates which are collectively complete gives back m *)
Lemma measFilter_pc {A} (m : Meas A) (l : seq (pred A)) :
  pc_pairwise_disj l -> pc_complete l (fun x => x \in measSupport m) ->
  m ~~ (measSum (map (fun f => measFilter m f) l)) @ 0.
  move: l m.
  induction l.
  induction m.
  rewrite //=.
  reflexivity.
  simpl.
  simpl in IHm.
  intros.
  caseOn (fst a == 0).
  intros.
  have: m ~~ [::] @ 0.
  apply IHm.
  done.
  rewrite /pc_complete.
  rewrite /pc_complete in H0.
  rewrite measSupport_cons in H0.
  rewrite H1 in H0.
  done.
  intros.
  rewrite /measEquiv; intros; rewrite pdist_le0.
  rewrite integ_cons.
  rewrite (eqP H1).
  have H3 := x f H2.
  rewrite pdist_le0 in H3.
  rewrite (eqP H3).
  rewrite !integ_nil.
  rewrite pmul0r padd0r; done.
  intros.
  rewrite /pc_complete in H0.
  have: a.2 \in measSupport (a :: m).
  rewrite measSupport_cons (negbTE H1) in_cons eq_refl orTb; done.
  intros.
  destruct (H0 _ x).
  destruct H2.
  inversion H2.


  
intros.
  simpl.
  have mH := measFilter_disj m a.
  etransitivity.
  apply mH.
  rewrite -(paddr0 0).
  apply measEquiv_app_cong.
  reflexivity.

  etransitivity.
  apply IHl.

  rewrite /pc_pairwise_disj.
  intros.
  apply H.
  apply List.in_cons; done.
  apply List.in_cons; done.
  intros.

  rewrite /pc_complete.
  intros.
  rewrite /pc_complete in H0.
  apply measSupport_measFilter in H1.
  move/andP: H1; elim; intros.
  destruct (H0 _ H1).
  destruct H3.
  exists x0.
  simpl in H3.
  destruct H3.
  subst.
  rewrite H4 in H2; done.
  split; done.

  have: [seq measFilter (measFilter m (fun x : A => ~~ a x)) f | f <- l] =
        [seq measFilter m f | f <- l].
  clear IHl H0 mH.
  induction l.
  done.
  simpl.
  rewrite IHl.
  congr (_ :: _).
  clear IHl.
  induction m.
  done.
  simpl.
  caseOn (a a1.2).
  intros.
  rewrite H0 //=.
  have: ~~ a0 a1.2.
  rewrite -(andbT (a0 a1.2)).
  rewrite -H0.
  apply H.
  apply List.in_cons.
  constructor; done.
  constructor; done.
  intros.
  rewrite (negbTE x).
  done.
  intro He; rewrite (negbTE He).
  simpl.
  caseOn (a0 a1.2).
  intro He2; rewrite He2.
  rewrite IHm; done.
  intro He2; rewrite (negbTE He2).
  done.
  rewrite /pc_pairwise_disj; intros.
  apply H.
  destruct H0.
  constructor; done.
  apply List.in_cons.
  apply List.in_cons.
  done.
  destruct H1.
  constructor; done.
  apply List.in_cons; apply List.in_cons; done.

  intros.
  rewrite x.
  reflexivity.
Qed.

  