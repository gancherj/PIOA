
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems StateSim.

  Definition tracePil {Act : finType} {P1 P2 : @PIOA Act} {H} : Trace (compPIOA P1 P2 H) -> Trace P1.
    elim.
    intros.
    constructor.
    apply (fst a).
    apply (filter (fun x => x \in cover (action P1)) b).
  Defined.

  Definition tracePir {Act : finType} {P1 P2 : @PIOA Act} {H} : Trace (compPIOA P1 P2 H) -> Trace P2.
    elim.
    intros.
    constructor.
    apply (snd a).
    apply (filter (fun x => x \in cover (action P2)) b).
  Defined.

  Definition traceInl {Act : finType} {P1 P2 : @PIOA Act} {H} : pQ P2 -> Trace P1 -> Trace (compPIOA P1 P2 H).
    intro; elim; intros; constructor.
    apply (a, X).
    apply b.
  Defined.

  Definition traceInr {Act : finType} {P1 P2 : @PIOA Act} {H} : pQ P1 -> Trace P2 -> Trace (compPIOA P1 P2 H).
    intro; elim; intros; constructor.
    apply (X ,a ).
    apply b.
  Defined.

Definition taskSplit {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (t : Task (compPIOA P1 P2 H)) :
  (Task P1) + (Task P2).
  destruct t.
  simpl in i.
  caseOn (tT \in pTO P1 :|: pTH P1).
  intro; left.
  econstructor.
  apply H0.
  caseOn (tT \in pTO P2 :|: pTH P2).
  intros; right; econstructor.
  apply H0.
  intros; exfalso.
  move/setUP: H0; move/orP; rewrite negb_or; move/andP; move => [h01 h02].
  move/setUP: H1; move/orP; rewrite negb_or; move/andP; move => [h11 h12].
  move/setUP: i; elim.
  move/setUP; elim.
  rewrite (negbTE h11); done.
  rewrite (negbTE h01); done.
  move/setUP; elim.
  rewrite (negbTE h12); done.
  rewrite (negbTE h02); done.
Defined.

Definition taskInjl {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (t : Task P1) :
  Task (compPIOA P1 P2 H).
  destruct t; econstructor.
  simpl.
  move/setUP: i; elim; intros.
  apply/setUP; left; apply/setUP; left; apply H0.
  apply/setUP; right; apply/setUP; left; apply H0.
Defined.

Definition taskInjr {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (t : Task P2) :
  Task (compPIOA P1 P2 H).
  destruct t; econstructor.
  simpl.
  move/setUP: i; elim; intros.
  apply/setUP; left; apply/setUP; right; apply H0.
  apply/setUP; right; apply/setUP; right; apply H0.
Defined.


Definition appTaskLeft {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (t : Task P1) mu := appTask (taskInjl _ P2 H t) mu.

Lemma meas_fmap_isSubdist {A B : eqType} (mu : Meas A) (f : A -> B) : isSubdist mu -> isSubdist (meas_fmap mu f).
  rewrite /isSubdist.
  rewrite /measMass.
  rewrite /meas_fmap.
  rewrite /measBind /measJoin /measSum.
  rewrite big_flatten !big_map.
  simpl.
  intros.
  have:  \big[padd/0]_(j <- mu) \big[padd/0]_(i <- [:: (j.1 * 1, f j.2)]) i.1 =
         \big[padd/0]_(j <- mu) j.1.
  apply eq_bigr; intros; rewrite big_cons big_nil.
  simpl.
  rewrite paddr0 pmulr1; done.
  intro He; rewrite He; done.
Qed.

Lemma compat_hidden_disabled {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (T : Task P1) x s:
  x \in T -> hiddenTask T -> ~~ enabled P2 s x.
  intros; apply/contraT; rewrite negbK; intros.

  have HC := actSetValid P2 s x H2.
  destruct H.
  move/setUP: HC; elim.
  move/setUP; elim; intros.

  move/disjointP: (H3 _ _ H1 (pI_in_action P2)).
  move/(_ _ H0).
  rewrite H5; done.

  move/bigcupP: H5; elim; intros.
  Check tO_in_action.
  move/disjointP: (H3 _ _ H1 (tO_in_action P2 _ H5)).
  move/(_ _ H0); rewrite H6; done.

  move/bigcupP; elim; intros.
  move/disjointP: (H3 _ _ H1 (tH_in_action P2 _ H5)).
  move/(_ _ H0).
  rewrite H6; done.
Qed.  


Lemma enabled_hiddenE {A} (P1 P2 : @PIOA A) H (T : Task P1) x s :
  x \in T -> hiddenTask T -> enabled P1 s.1 x =
                             enabled (compPIOA P1 P2 H) s x.
  intros.

  simpl.
  have: tr P2 s.2 x = None.
  remember (tr P2 s.2 x) as eta; destruct eta.
  exfalso; apply/negP. eapply compat_hidden_disabled.
  apply H.
  apply H0.
  done.
  instantiate (1 := s.2); rewrite /enabled -Heqeta //=.
  done.
  intros.
  rewrite /enabled //= /prePIOA_comptrans.
  rewrite x0.
  have: x \notin cover (action P2).
  destruct H.
  apply/contraT; rewrite negbK; intros.
  move/bigcupP: H4; elim; intros.
  move/disjointP: (H2 _ _ H1 H4).
  move/(_ _ H0).
  rewrite H5; done.
  intro.
  rewrite x1.
  destruct (tr P1 s.1 x); done.
Qed.

Lemma compPIOA_pI_sym {A} (P1 P2 : @PIOA A) H H2 :
  pI (compPIOA P1 P2 H) = pI (compPIOA P2 P1 H2).
  simpl.
  rewrite (setUC (pI P1) (pI P2)).
  rewrite (setUC (pTO P1) (pTO P2)).
  done.
Qed.

Lemma compPIOA_pTO_sym {A} (P1 P2 : @PIOA A) H H2 :
  pTO (compPIOA P1 P2 H) = pTO (compPIOA P2 P1 H2).
  by rewrite //= setUC.
Qed.

Lemma compPIOA_pTH_sym {A} (P1 P2 : @PIOA A) H H2 :
  pTH (compPIOA P1 P2 H) = pTH (compPIOA P2 P1 H2).
  by rewrite //= setUC.
Qed.

Check enabled.

Check tr.

Lemma measBind_swap {A B C : eqType} (D1 : Meas A) (D2 : Meas B) (D3 : A -> B -> Meas C) :
  (x <- D1; y <- D2; D3 x y) ~~ (y <- D2; x <- D1; D3 x y) @ 0.
  rewrite /measEquiv; intros.
  rewrite pdist_le0.
  rewrite /integ /measBind /measJoin /measSum //=.
  rewrite !big_flatten !big_map.
  simpl.
  rewrite /measScale.
  apply/eqP.
  etransitivity.
  apply eq_bigr; intros.
  rewrite big_map big_flatten !big_map //.
  simpl.
  rewrite exchange_big.
  apply eq_bigr; intros.
  rewrite big_map big_flatten !big_map //.
  apply eq_bigr; intros.
  rewrite !big_map.
  simpl.
  apply eq_bigr; intros.
  rewrite !pmulrA.
  rewrite (pmulrC i0.1 i.1).
  done.
Qed.

Lemma compPIOA_tr_sym {A} (P1 P2 : @PIOA A) x s :
  (tr (comp_prePIOA P2 P1) s x = None <-> (tr (comp_prePIOA P1 P2) (s.2, s.1) x = None)) /\
  (forall mu eta, tr (comp_prePIOA P2 P1) s x = Some mu -> tr (comp_prePIOA P1 P2) (s.2, s.1) x = Some eta ->
   mu ~~ meas_fmap eta (fun p => (p.2, p.1)) @ 0).

  simpl.
  rewrite /prePIOA_comptrans.
  simpl.
  split; [idtac | intros mu eta];
  remember (tr P1 s.2 x) as D; destruct D;
  remember (tr P2 s.1 x) as D'; destruct D'.
  split; congruence.
  destruct (x \notin cover (action P2)); split; try congruence.
  done.
  done.
  destruct (x \notin cover (action P1)); split; try congruence.
  done.
  done.
  done.
  simpl.
  intros H1 H2; injection H1; injection H2; intros; subst.
  rewrite /meas_fmap.
  dsimp.
  rewrite measBind_swap.
  apply measBind_cong_r; intros.
  rewrite bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet //=.
  reflexivity.
  eapply tr_subDist; symmetry in HeqD'; apply HeqD'.
  eapply tr_subDist; symmetry in HeqD; apply HeqD.
  destruct (x \notin cover (action P2)).
  intros H1 H2; injection H1; injection H2; intros; subst.
  rewrite /meas_fmap.
  rewrite bindAssoc.
  apply measBind_cong_r; intros; dsimp.
  eapply tr_subDist; symmetry in HeqD; apply HeqD.
  congruence.
  destruct (x \notin cover (action P1)).
  intros H1 H2; injection H1; injection H2; intros; subst.
  rewrite /meas_fmap.
  rewrite bindAssoc.
  apply measBind_cong_r; intros; dsimp.
  eapply tr_subDist; symmetry in HeqD'; apply HeqD'.
  congruence.
  congruence.
Qed.


Lemma compPIOA_enabled_symm {A} (P1 P2 : @PIOA A) H H2 x s:
  enabled (compPIOA P1 P2 H) s x =
  enabled (compPIOA P2 P1 H2) (s.2, s.1) x.
  rewrite /enabled.
  destruct (compPIOA_tr_sym P2 P1 x s).
  remember (tr (compPIOA P1 P2 H) s x) as mu; destruct mu.
  remember (tr (compPIOA P2 P1 H2) (s.2,s.1) x) as eta; destruct eta.
  done.
  symmetry in Heqeta;
  apply H0 in Heqeta.
  rewrite Heqeta in Heqmu; done.
  destruct H0.
  symmetry in Heqmu; rewrite (H0 Heqmu); done.
Qed.

Definition compPIOA_task_sym {A} (P1 P2 : @PIOA A) H H2 :
  Task (compPIOA P1 P2 H) ->
  Task (compPIOA P2 P1 H2).
  intro T; destruct T.
  econstructor.
  rewrite compPIOA_pTO_sym.
  rewrite compPIOA_pTH_sym.
  apply i.
Defined.


Definition compPIOA_appTask_sym {A} (P1 P2 : @PIOA A) H H2 T mu : isSubdist mu ->
  appTask T mu ~~
  meas_fmap (appTask (compPIOA_task_sym P1 P2 H H2 T) (x <- mu; ret ((x.1.2, x.1.1), x.2))) (fun x => ((x.1.2, x.1.1), x.2)) @ 0.
  intro Hsubmu.
  rewrite /appTask.
  rewrite /meas_fmap.
  rewrite !bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet; simpl.
  rewrite /runTask.
  have:  [pick x0 in T  | enabled (compPIOA P1 P2 H) x.1 x0] =
         [pick x0 in compPIOA_task_sym P1 P2 H H2 T  | enabled (compPIOA P2 P1 H2) (x.1.2, x.1.1) x0].  
  
  {
    apply eq_pick.
    move=> z.
    rewrite /compPIOA_task_sym; simpl.
    rewrite compPIOA_enabled_symm.
    destruct T; simpl.
    done.
    done.
  }

  intros.
  rewrite -x0.
  case: pickP; intros.

  destruct (compPIOA_tr_sym P1 P2  x1 (x.1.2, x.1.1)).


  remember (tr (compPIOA P1 P2 H) x.1 x1) as D; destruct D; symmetry in HeqD.
  remember (tr (compPIOA P2 P1 H2) (x.1.2, x.1.1) x1) as D'; destruct D'; symmetry in HeqD'.
  have Heq := H3 _ _ HeqD' HeqD.
  rewrite HeqD HeqD'.
  simpl.
  rewrite bindAssoc (measBind_cong_l Heq).
  rewrite /external.
  rewrite compPIOA_pI_sym compPIOA_pTO_sym.
  destruct (x1 \in pI (compPIOA P2 P1 H2) :|: cover (pTO (compPIOA P2 P1 H2))).
  rewrite /meas_fmap bindAssoc.
  apply measBind_cong_r; intros.
  rewrite !bindRet.
  simpl.
  destruct x2;
  reflexivity.

  eapply (@tr_subDist _ (compPIOA P1 P2 H) _ _).
  apply HeqD.
  rewrite /meas_fmap bindAssoc.
  apply measBind_cong_r; intros.
  rewrite !bindRet //=.
  destruct x2; reflexivity.
  eapply (@tr_subDist _ (compPIOA P1 P2 H) _ _).
  apply HeqD.
  intros.
  destruct (x1 \in external (compPIOA P2 P1 H2)).
  dsubdist.
  intros; dsubdist.
  dsubdist.
  intros; dsubdist.
  destruct H1.
  simpl in H1.
  have Hq := H1 HeqD'.
  simpl in HeqD.
  destruct x.1.
  remember x.1 as p; destruct p.
  rewrite -Heqp in HeqD.
  rewrite -Heqp in Hq.
  simpl in Hq.
  rewrite Hq in HeqD; done.
  destruct H1.
  simpl in H4.
  simpl in HeqD.
  have Hq := H4 HeqD.
  simpl.
  rewrite HeqD.
  rewrite Hq.
  rewrite bindRet.
  simpl.
  destruct x; simpl.
  destruct s; simpl.
  reflexivity.
  rewrite bindRet.
  simpl.
  destruct x; simpl.
  destruct s; simpl.
  reflexivity.
  done.
Qed.


Section CompPIOA_symm.
  Context {A : finType}.
  Context (P1 P2 : @PIOA A).
  Context (Hc : Compatible P1 P2).
  Context (ic : inputClosed (compPIOA P1 P2 Hc)).

  Lemma inputClosed_sym : inputClosed (compPIOA P2 P1 (compatible_sym _ _ Hc)).
    rewrite /inputClosed.
    rewrite compPIOA_pI_sym; done.
  Qed.

  Lemma compPIOA_sym : @refinement _ (compPIOA P1 P2 Hc) (compPIOA P2 P1 (compatible_sym _ _ Hc)) ic inputClosed_sym 0.
    eapply stateSimSound.
    admit.
  Admitted.
End CompPIOA_symm.

Section CompPIOA_assoc.
  Context {A : finType}.
  Context (P1 P2 P3 : @PIOA A).
  Context (Hc1 : Compatible P2 P3).
  Context (Hc2 : Compatible P1 (compPIOA P2 P3 Hc1)).
  Context (Hc3 : Compatible P1 P2).
  Context (Hc4 : Compatible (compPIOA P1 P2 Hc3) P3).
  Context (ic : inputClosed (compPIOA (compPIOA P1 P2 Hc3) P3 Hc4)).

  Definition Q1 := compPIOA P1 (compPIOA P2 P3 Hc1) Hc2.
  Definition Q2 := compPIOA (compPIOA P1 P2 Hc3) P3 Hc4.

  Lemma coverU {X : finType} (F G : {set {set X}}) :
    cover (F :|: G) = cover F :|: cover G.
    rewrite /cover bigcup_setU //=.
  Qed.

  Lemma pI_comp_assoc : pI Q1 = pI Q2.
    simpl.
    rewrite !setUA.
    rewrite !setDUl //=.
    rewrite !setUA.
    congr (_ :|: _ :|: _).
    rewrite !coverU.
    rewrite !setDDl.
    congr (_ :\: _).
    admit.
    rewrite !coverU.
    rewrite !setDDl.
    congr (_ :\: _).
    admit.
    rewrite !coverU.
    rewrite !setDDl.
    congr (_ :\: _).
    admit.
  Admitted.

  Lemma inputClosed_assoc : inputClosed (compPIOA P1 (compPIOA P2 P3 Hc1) Hc2).
    rewrite /inputClosed.
    rewrite pI_comp_assoc.
    apply ic.
  Qed.

  Lemma compPIOA_assoc : @refinement _ Q2 Q1 ic inputClosed_assoc 0.
    admit.
  Admitted.
End CompPIOA_assoc.