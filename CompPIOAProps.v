
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems.

  Lemma coverU {X : finType} (F G : {set {set X}}) :
    cover (F :|: G) = cover F :|: cover G.
    rewrite /cover bigcup_setU //=.
  Qed.

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

  Check tr.

Inductive comp_tr_specI {A} (P1 P2 : @PIOA A) H s x (Hx : x \in cover (action (compPIOA P1 P2 H))) : Prop :=
  | enabled_hidden_l : forall mu, x \in cover (pTH P1) -> tr P2 s.2 x = None -> tr P1 s.1 x = Some mu -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; ret (a, s.2)) -> comp_tr_specI P1 P2 H s x Hx

  | enabled_hidden_r : forall mu, x \in cover (pTH P2) -> tr P1 s.1 x = None -> tr P2 s.2 x = Some mu -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; ret (s.1, a)) -> comp_tr_specI P1 P2 H s x Hx

  | enabled_input_l : forall mu, x \in pI P1 -> x \notin pI P2 -> tr P1 s.1 x = Some mu -> tr P2 s.2 x = None -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; ret (a, s.2)) -> comp_tr_specI P1 P2 H s x Hx                         

  | enabled_input_r : forall mu, x \in (pI P2) -> x \notin pI P1 -> tr P1 s.1 x = None -> tr P2 s.2 x = Some mu -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; ret (s.1, a)) -> comp_tr_specI P1 P2 H s x Hx  

  | enabled_input_lr : forall mu eta, x \in (pI P1) -> x \in (pI P2) -> tr P1 s.1 x = Some mu -> tr P2 s.2 x = Some eta -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; b <- eta; ret (a,b)) -> comp_tr_specI P1 P2 H s x Hx

  | enabled_output_ext_l : forall mu, x \in cover (pTO P1) -> x \notin pI P2 -> tr P2 s.2 x = None -> tr P1 s.1 x = Some mu -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; ret (a, s.2)) -> comp_tr_specI P1 P2 H s x Hx

  | enabled_output_ext_r : forall mu, x \in cover (pTO P2) -> x \notin pI P1 -> tr P1 s.1 x = None -> tr P2 s.2 x = Some mu -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; ret (s.1, a)) -> comp_tr_specI P1 P2 H s x Hx

  | enabled_comm_l : forall mu eta, x \in cover (pTO P1) -> x \in pI P2 -> tr P1 s.1 x = Some mu -> tr P2 s.2 x = Some eta -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; b <- eta; ret (a,b)) -> comp_tr_specI P1 P2 H s x Hx  

  | enabled_comm_r : forall mu eta, x \in cover (pTO P2) -> x \in pI P1 -> tr P1 s.1 x = Some mu -> tr P2 s.2 x = Some eta -> tr (compPIOA P1 P2 H) s x = Some (a <- mu; b <- eta; ret (a,b)) -> comp_tr_specI P1 P2 H s x Hx                                                                                    
                                                                                                                                                                                                               | disabled_lr : tr P1 s.1 x = None -> tr P2 s.2 x = None -> tr (compPIOA P1 P2 H) s x = None -> comp_tr_specI P1 P2 H s x Hx

  | disabled_l : forall mu, tr P1 s.1 x = Some mu -> tr P2 s.2 x = None -> x \in cover (action P2) -> tr (compPIOA P1 P2 H) s x = None -> comp_tr_specI P1 P2 H s x Hx

  | disabled_r : forall mu, tr P2 s.2 x = Some mu -> tr P1 s.1 x = None -> x \in cover (action P1) -> tr (compPIOA P1 P2 H) s x = None -> comp_tr_specI P1 P2 H s x Hx.

Lemma comp_tr_spec {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) s x Hx :
  comp_tr_specI P1 P2 H s x Hx.
  remember (tr (compPIOA P1 P2 H) s x) as nu.
  destruct nu.
 simpl in Heqnu.
 rewrite /prePIOA_comptrans in Heqnu.

 remember (tr P1 s.1 x) as mu; symmetry in Heqmu.
 remember (tr P2 s.2 x) as eta; symmetry in Heqeta.
 destruct mu; destruct eta.

 have: enabled P1 s.1 x.
 rewrite /enabled Heqmu //=.
 intro He1.

 have: enabled P2 s.2 x.
 rewrite /enabled Heqeta //=.
 intro He2.

 Check actSetValid.
 have AV1 := actSetValid P1 s.1 x He1.
 have AV2 := actSetValid P2 s.2 x He2.

 move/setUP: AV1; elim; [ move/setUP; elim | idtac]; intros.
 move/setUP: AV2; elim; [ move/setUP; elim | idtac]; intros.
 eapply enabled_input_lr; try done.
 apply Heqmu.
 apply Heqeta.
 rewrite //= /prePIOA_comptrans  Heqmu Heqeta //=.
 eapply enabled_comm_r; try done.
 apply Heqmu.
 apply Heqeta.
 rewrite //= /prePIOA_comptrans  Heqmu Heqeta //=.
 
 move/bigcupP: H1; elim; intros.
 destruct H.
 move/disjointP: (i1 _ _ H1 (pI_in_action P1)).
 move/(_ _ H2); rewrite H0; done.

 move/setUP: AV2; elim; [ move/setUP; elim | idtac]; intros.

 eapply enabled_comm_l.
 done.
 done.
 apply Heqmu.
 apply Heqeta.
 rewrite //= /prePIOA_comptrans Heqmu Heqeta //=.
 destruct H.
 move/bigcupP: H0; elim; intros.
 move/bigcupP: H1; elim; intros.
 move/disjointP: (i _ _ H H1).
 move/(_ _ H0); rewrite H2; done.

 move/bigcupP: H0; elim; intros.
 move/bigcupP: H1; elim; intros.

 destruct H.
 move/disjointP: (i1 _ _ H1 (tO_in_action P1 _ H0)).
 move/(_ _ H3); rewrite H2; done.

 destruct H.
 move/setUP: AV2; elim.
 move/setUP; elim; intros.
 move/bigcupP: H0; elim; intros.
 move/disjointP: (i0 _ _ H0 (pI_in_action P2)).
 move/(_ _ H1); rewrite H; done.
 move/bigcupP: H0; elim; intros; move/bigcupP: H; elim; intros.
 move/disjointP: (i0 _ _ H0 (tO_in_action P2 _ H)).
 move/(_ _ H1); rewrite H2; done.

 move/bigcupP; elim; intros.
 move/bigcupP: H0; elim; intros.
 move/disjointP: (i0 _ _ H0 (tH_in_action P2 _ H)).
 move/(_ _ H2); rewrite H1; done.


 (* left enabled, not right *)

 have: ~~ enabled P2 s.2 x.
 rewrite /enabled Heqeta //=.
 intros Hne2.

 have: x \notin cover (action P2).
 apply/contraT; intro Hc; rewrite (negbTE Hc) in Heqnu; done.
 intros.


 rewrite /cover /action !bigcup_setU in x0.
 move/setUP/orP: x0; rewrite negb_or; move/andP; elim.
 move/setUP/orP; rewrite negb_or; move/andP; elim; intros.


 have: enabled P1 s.1 x.
 rewrite /enabled Heqmu //=.
 intros He1.


 have AV1 := actSetValid P1 s.1 x He1.
 move/setUP: AV1; elim.
 move/setUP; elim; intros.

 eapply enabled_input_l.
 done.
 rewrite big_set1 in H0; done.
 apply Heqmu.

 rewrite //= /prePIOA_comptrans //=.
 rewrite //= /prePIOA_comptrans //=.

 rewrite Heqmu Heqeta.
 caseOn (x \notin cover (action P2)).
 intro Hn; rewrite Hn //=.
 rewrite negbK; intro Hn; rewrite Hn in Heqnu; done.


 eapply enabled_output_ext_l.
 done.
 rewrite big_set1 in H0; done.
 rewrite /enabled Heqeta; done.
 apply Heqmu.

 rewrite //= /prePIOA_comptrans //=.
 rewrite Heqmu Heqeta.
 caseOn (x \notin cover (action P2)); intro Hn; [rewrite Hn; done | rewrite (negbTE Hn) in Heqnu; done].
 intro; eapply enabled_hidden_l.
 done.
 rewrite /enabled Heqeta //=.
 apply Heqmu.
 rewrite //= /prePIOA_comptrans //=.
 rewrite Heqmu Heqeta.
 caseOn (x \notin cover (action P2)); intro Hn; [rewrite Hn; done | rewrite (negbTE Hn) in Heqnu; done].

 (* right enabled, not left *)

 have: ~~ enabled P1 s.1 x.
 rewrite /enabled Heqmu //=.
 intros Hne1.

 have: x \notin cover (action P1).
 apply/contraT; intro Hc; rewrite (negbTE Hc) in Heqnu; done.
 intros.


 rewrite /cover /action !bigcup_setU in x0.
 move/setUP/orP: x0; rewrite negb_or; move/andP; elim.
 move/setUP/orP; rewrite negb_or; move/andP; elim; intros.


 have: enabled P2 s.2 x.
 rewrite /enabled Heqeta //=.
 intros He2.


 have AV2 := actSetValid P2 s.2 x He2.
 move/setUP: AV2; elim.
 move/setUP; elim; intros.

 eapply enabled_input_r.
 done.
 rewrite big_set1 in H0; done.
 rewrite /enabled Heqmu //=.
 apply Heqeta.

 rewrite //= /prePIOA_comptrans //=.
 rewrite Heqmu Heqeta.
 caseOn (x \notin cover (action P1)).
 intro Hn; rewrite Hn //=.
 rewrite negbK; intro Hn; rewrite Hn in Heqnu; done.


 eapply enabled_output_ext_r.
 done.
 rewrite big_set1 in H0; done.
 rewrite /enabled Heqmu; done.
 apply Heqeta.

 rewrite //= /prePIOA_comptrans //=.
 rewrite Heqmu Heqeta.
 caseOn (x \notin cover (action P1)); intro Hn; [rewrite Hn; done | rewrite (negbTE Hn) in Heqnu; done].
 intro; eapply enabled_hidden_r.
 done.
 rewrite /enabled Heqmu //=.
 apply Heqeta.
 rewrite //= /prePIOA_comptrans //=.
 rewrite Heqmu Heqeta.
 caseOn (x \notin cover (action P1)); intro Hn; [rewrite Hn; done | rewrite (negbTE Hn) in Heqnu; done].

 apply disabled_lr; done.


 remember (tr P1 s.1 x) as eta; remember (tr P2 s.2 x) as mu; symmetry in Heqeta; symmetry in Heqmu.
 destruct eta; destruct mu.
 rewrite //= /prePIOA_comptrans Heqeta Heqmu in Heqnu.
 done.
 eapply disabled_l.
 apply Heqeta.
 done.
 rewrite //= /prePIOA_comptrans Heqeta Heqmu in Heqnu.
 apply/contraT; intros.
 rewrite H0 in Heqnu; done.
 done.
 eapply disabled_r.
 apply Heqmu.
 done.
 rewrite //= /prePIOA_comptrans Heqeta Heqmu in Heqnu.
 apply/contraT; intros.
 rewrite H0 in Heqnu; done.
 done.
 apply disabled_lr; done.
Qed.

Lemma compPIOA_tr_sym {A} (P1 P2 : @PIOA A) H x s : x \in cover (action (compPIOA P1 P2 H)) ->
  (tr (comp_prePIOA P1 P2) s x = None <-> (tr (comp_prePIOA P2 P1) (s.2, s.1) x = None)) /\
  (forall mu eta, tr (comp_prePIOA P1 P2) s x = Some mu -> tr (comp_prePIOA P2 P1) (s.2, s.1) x = Some eta ->
   mu ~~ meas_fmap eta (fun p => (p.2, p.1)) @ 0).
  intros; split.
  rewrite //= /prePIOA_comptrans //=.
  remember (tr P1 s.1 x) as mu; remember (tr P2 s.2 x) as eta; destruct mu; destruct eta.
  done.
  caseOn (x \in cover (action P2)); intro Hc; rewrite Hc; done.
  caseOn (x \in cover (action P1)); intro Hc; rewrite Hc; done.
  done.

  rewrite //= /prePIOA_comptrans //=.
  remember (tr P1 s.1 x) as mu; remember (tr P2 s.2 x) as eta; destruct mu; destruct eta.
  intros.
  inversion H1; inversion H2; subst.
  rewrite /meas_fmap; dsimp.
  rewrite measBind_swap.
  apply measBind_cong_r; intros.
  rewrite bindAssoc; apply measBind_cong_r; intros.
  rewrite bindRet; reflexivity.
  eapply tr_subDist; symmetry; apply Heqmu.
  eapply tr_subDist; symmetry; apply Heqeta.
  intros.
  caseOn (x \in cover (action P2)).
  intro Hc; rewrite Hc in H1; done.
  intro Hc; rewrite Hc in H1; rewrite Hc in H2.
  inversion H1; inversion H2; subst.

  rewrite /meas_fmap bindAssoc; apply measBind_cong_r; intros.
  rewrite bindRet; reflexivity.
  eapply tr_subDist; symmetry; apply Heqmu.

  intros.
  caseOn (x \in cover (action P1)).
  intro Hc; rewrite Hc in H1; done.
  intro Hc; rewrite Hc in H1; rewrite Hc in H2.
  inversion H1; inversion H2; subst.

  rewrite /meas_fmap bindAssoc; apply measBind_cong_r; intros.
  rewrite bindRet; reflexivity.
  eapply tr_subDist; symmetry; apply Heqeta.
  done.
Qed.


  Lemma compTaskP {A} {P1 P2 : @PIOA A} {H : Compatible P1 P2} (t : Task A) :
    t \in (Tasks (compPIOA P1 P2 H)) -> (t \in Tasks P1) || (t \in Tasks P2).
    rewrite /Tasks //=.

  have: pTO P1 :|: pTO P2 :|: (pTH P1 :|: pTH P2) =
        (pTO P1 :|: pTH P1) :|: (pTO P2 :|: pTH P2).
  rewrite !setUA.
  congr (_ :|: _).
  rewrite -setUA.
  rewrite -setUA.
  congr (_ :|: _).
  rewrite setUC; done.
  intro.
  rewrite x.
  move/setUP/orP; done.
  Qed.

Definition taskInjl {A} {P1 P2 : @PIOA A} {H : Compatible P1 P2} (t : Task A) :
  t \in Tasks P1 -> t \in Tasks (compPIOA P1 P2 H).
  rewrite /Tasks //=.
  move/setUP; elim.
  intro; apply/setUP; left; apply/setUP; left; done.
  intro; apply/setUP; right; apply/setUP; left; done.
Defined.

Definition taskInjr {A} {P1 P2 : @PIOA A} {H : Compatible P1 P2} (t : Task A) :
  t \in Tasks P2 -> t \in Tasks (compPIOA P1 P2 H).
  rewrite /Tasks //=.
  move/setUP; elim.
  intro; apply/setUP; left; apply/setUP; right; done.
  intro; apply/setUP; right; apply/setUP; right; done.
Defined.

Lemma compat_hidden_disabled {A} (P1 P2 : @PIOA A) (H : Compatible P1 P2) (T : Task A) x s:
  T \in (pTH P1) -> x \in T -> ~~ enabled P2 s x.
  intros; apply/contraT; rewrite negbK; intros.

  have HC := actSetValid P2 s x H2.
  destruct H.
  move/setUP: HC; elim.
  move/setUP; elim; intros.

  move/disjointP: (H3 _ _ H0 (pI_in_action P2)).
  move/(_ _ H1).
  rewrite H5; done.

  move/bigcupP: H5; elim; intros.
  move/disjointP: (H3 _ _ H0 (tO_in_action P2 _ H5)).
  move/(_ _ H1); rewrite H6; done.

  move/bigcupP; elim; intros.
  move/disjointP: (H3 _ _ H0 (tH_in_action P2 _ H5)).
  move/(_ _ H1).
  rewrite H6; done.
Qed.  


Lemma enabled_hidden_compE {A} (P1 P2 : @PIOA A) H (T : Task A) x s :
  T \in (pTH P1) -> x \in T -> enabled P1 s.1 x =
                             enabled (compPIOA P1 P2 H) s x.
  intros.

  simpl.
  have: tr P2 s.2 x = None.
  remember (tr P2 s.2 x) as eta; destruct eta.
  exfalso; apply/negP. eapply compat_hidden_disabled.
  apply H.
  apply H0.
  apply H1.
  instantiate (1 := s.2); rewrite /enabled -Heqeta //=.
  done.
  intros.
  rewrite /enabled //= /prePIOA_comptrans.
  rewrite x0.
  have: x \notin cover (action P2).
  destruct H.
  apply/contraT; rewrite negbK; intros.
  move/bigcupP: H4; elim; intros.
  move/disjointP: (H2 _ _ H0 H4).
  move/(_ _ H1).
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

Lemma compPIOA_enabled_sym {A} (P1 P2 : @PIOA A) H H2 s x :
  enabled (compPIOA P1 P2 H) s x = enabled (compPIOA P2 P1 H2) (s.2, s.1) x.
rewrite /enabled //= /prePIOA_comptrans.
remember (tr P1 s.1 x) as mu; remember (tr P2 s.2 x) as eta; destruct mu; destruct eta; rewrite -Heqmu -Heqeta.
done.
caseOn (x \in cover (action P2)); intro Hc; rewrite Hc; done.
caseOn (x \in cover (action P1)); intro Hc; rewrite Hc; done.
done.
Qed.


Definition compPIOA_appTask_sym {A} (P1 P2 : @PIOA A) H H2 T mu : isSubdist mu ->
  T \in Tasks (compPIOA P1 P2 H) ->
  appTask (compPIOA P1 P2 H) T mu ~~
  meas_fmap (appTask (compPIOA P2 P1 H2) T (x <- mu; ret ((x.1.2, x.1.1), x.2))) (fun x => ((x.1.2, x.1.1), x.2)) @ 0.
  intros Hsubmu HTin.
  intros.
  rewrite /appTask.
  rewrite /meas_fmap.
  rewrite !bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet; simpl.
  rewrite /runTask.
  have:  [pick x0 in T  | enabled (compPIOA P1 P2 H) x.1 x0] =
         [pick x0 in T  | enabled (compPIOA P2 P1 H2) (x.1.2, x.1.1) x0].  
  
  {
    apply eq_pick.
    move=> z.
    simpl.
    rewrite compPIOA_enabled_sym.
    done.
    done.
  }


  intros.
  rewrite -x0.
  case: pickP; intros.

  destruct (compPIOA_tr_sym P1 P2  H x1 x.1).

  apply/bigcupP.
  exists T.

  (* TODO HERE *)




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

(* 

Section ParaStateInj.
  Context {A : finType}.
  Context (P1 P2 Adv : @PIOA A).
  Context (Hc1 : Compatible P1 Adv).
  Context (Hc2 : Compatible P2 Adv).
  Context (Hine : pI P1 = pI P2).
  Check tr.

  Record ParaStateInj (R : pQ P1 -> pQ P2) :=
    {
      piInput : forall s x, x \in pI P1 ->
                                  match tr P1 s x, tr P2 (R s) x with
                                  | Some mu, Some eta => meas_fmap mu R ~~ eta @ 0
                                  | _, _ => false
                                           end;
      piStart : R (start _) = (start _);
      piStep : forall T mu eta,
          meas_fmap mu (fun p => (R p.1, p.2)) ~~ eta @ 0 ->
          exists ts,
            meas_fmap (appTask T mu) (fun p => (R p.1, p.2)) ~~
                      runPIOA _ ts eta @ 0
                      }.

  Context (ic1 : inputClosed (compPIOA P1 Adv Hc1)).
  Context (ic2 : inputClosed (compPIOA P2 Adv Hc2)).

  Lemma paraStateSound R : ParaStateInj R -> @refinement _ (compPIOA P1 Adv Hc1) (compPIOA P2 Adv Hc2) ic1 ic2 0.
    intros.
    eapply stateSimSound.
    instantiate (1 := fun p => (R p.1, p.2)).
    destruct H; constructor.
    simpl.
    rewrite piStart0; done.
    intros.
    destruct T.
    simpl in i.
    elim (setUP i).
    move/setUP; elim.
    intros.
    Check Build_Task.
    have: tT \in pTO P1 :|: pTH P1.
    apply/setUP; left; done.
    intro x.
    have: meas_fmap (meas_fmap mu (fun x => (x.1.1, x.2))) (fun p => (R p.1, p.2)) ~~
          meas_fmap eta (fun x => (x.1.1, x.2)) @ 0.
    admit.
    intro xeq.
    destruct (piStep0 (Build_Task _ _ _ x) (meas_fmap mu (fun x => (x.1.1, x.2))) (meas_fmap eta (fun x => (x.1.1, x.2))) xeq).
    exists (map (fun t => taskInjl _ _ _ t) x0).
    simpl in H1.
    simpl.
    admit.
    intros.
    have: tT \in pTO Adv :|: pTH Adv.
    apply/setUP; left; done.
    intro.
    exists (map (taskInjr _ _ _) (Build_Task _ _ _ x :: nil)).
    simpl.
    admit.


    (* hidden *)
    admit.
    Admitted.

          



*)