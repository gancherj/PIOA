
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat.

Require Import PIOA Meas Posrat CompPIOA Lems StateSim.

Section compPIOAProps.
  Context {A : finType} (P1 P2 : @PIOA A) (p1p2 : P1 ||| P2).

  Lemma coverU {X : finType} (F G : {set {set X}}) :
    cover (F :|: G) = cover F :|: cover G.
    rewrite /cover bigcup_setU //=.
  Qed.

  Definition tracePil {Act : finType} : Trace p1p2 -> Trace P1.
    elim.
    intros.
    constructor.
    apply (fst a).
    apply (filter (fun x => x \in cover (action P1)) b).
  Defined.

  Definition tracePir {Act : finType} : Trace p1p2 -> Trace P2.
    elim.
    intros.
    constructor.
    apply (snd a).
    apply (filter (fun x => x \in cover (action P2)) b).
  Defined.

  Definition traceInl {Act : finType} : pQ P2 -> Trace P1 -> Trace p1p2.
    intro; elim; intros; constructor.
    apply (a, X).
    apply b.
  Defined.

  Definition traceInr {Act : finType} : pQ P1 -> Trace P2 -> Trace p1p2.
    intro; elim; intros; constructor.
    apply (X ,a ).
    apply b.
  Defined.


Inductive comp_tr_specI s x (Hx : x \in cover (action p1p2)) : Prop :=
  | enabled_hidden_l : forall mu, x \in cover (pTH P1) -> tr P2 s.2 x = None -> tr P1 s.1 x = Some mu -> tr p1p2 s x = Some (a <- mu; ret (a, s.2)) -> comp_tr_specI s x Hx

  | enabled_hidden_r : forall mu, x \in cover (pTH P2) -> tr P1 s.1 x = None -> tr P2 s.2 x = Some mu -> tr p1p2 s x = Some (a <- mu; ret (s.1, a)) -> comp_tr_specI s x Hx

  | enabled_input_l : forall mu, x \in pI P1 -> x \notin pI P2 -> tr P1 s.1 x = Some mu -> tr P2 s.2 x = None -> tr p1p2 s x = Some (a <- mu; ret (a, s.2)) -> comp_tr_specI s x Hx                         

  | enabled_input_r : forall mu, x \in (pI P2) -> x \notin pI P1 -> tr P1 s.1 x = None -> tr P2 s.2 x = Some mu -> tr p1p2 s x = Some (a <- mu; ret (s.1, a)) -> comp_tr_specI s x Hx  

  | enabled_input_lr : forall mu eta, x \in (pI P1) -> x \in (pI P2) -> tr P1 s.1 x = Some mu -> tr P2 s.2 x = Some eta -> tr p1p2 s x = Some (a <- mu; b <- eta; ret (a,b)) -> comp_tr_specI s x Hx

  | enabled_output_ext_l : forall mu, x \in cover (pTO P1) -> x \notin pI P2 -> tr P2 s.2 x = None -> tr P1 s.1 x = Some mu -> tr p1p2 s x = Some (a <- mu; ret (a, s.2)) -> comp_tr_specI s x Hx

  | enabled_output_ext_r : forall mu, x \in cover (pTO P2) -> x \notin pI P1 -> tr P1 s.1 x = None -> tr P2 s.2 x = Some mu -> tr p1p2 s x = Some (a <- mu; ret (s.1, a)) -> comp_tr_specI s x Hx

  | enabled_comm_l : forall mu eta, x \in cover (pTO P1) -> x \in pI P2 -> tr P1 s.1 x = Some mu -> tr P2 s.2 x = Some eta -> tr p1p2 s x = Some (a <- mu; b <- eta; ret (a,b)) -> comp_tr_specI s x Hx  

  | enabled_comm_r : forall mu eta, x \in cover (pTO P2) -> x \in pI P1 -> tr P1 s.1 x = Some mu -> tr P2 s.2 x = Some eta -> tr p1p2 s x = Some (a <- mu; b <- eta; ret (a,b)) -> comp_tr_specI s x Hx                                                                                    
                                                                                                                                                                                                               | disabled_lr : tr P1 s.1 x = None -> tr P2 s.2 x = None -> tr p1p2 s x = None -> comp_tr_specI s x Hx

  | disabled_l : forall mu, tr P1 s.1 x = Some mu -> tr P2 s.2 x = None -> x \in cover (action P2) -> tr p1p2 s x = None -> comp_tr_specI s x Hx

  | disabled_r : forall mu, tr P2 s.2 x = Some mu -> tr P1 s.1 x = None -> x \in cover (action P1) -> tr p1p2 s x = None -> comp_tr_specI s x Hx.

Lemma comp_tr_spec s x Hx :
  comp_tr_specI s x Hx.
  remember (tr p1p2 s x) as nu.
  destruct nu.
  set H := 0.
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
 destruct p1p2.
 move/disjointP: (forall_inP (forall_inP i1 _ H1) _ (pI_in_action P1)).
 move/(_ _ H2); rewrite H0; done.

 move/setUP: AV2; elim; [ move/setUP; elim | idtac]; intros.

 eapply enabled_comm_l.
 done.
 done.
 apply Heqmu.
 apply Heqeta.
 rewrite //= /prePIOA_comptrans Heqmu Heqeta //=.
 destruct p1p2.
 move/bigcupP: H0; elim; intros.
 move/bigcupP: H1; elim; intros.
 move/disjointP: (forall_inP (forall_inP i _ H0) _ H1).
 move/(_ _ H2); rewrite H3; done.

 move/bigcupP: H0; elim; intros.
 move/bigcupP: H1; elim; intros.

 destruct p1p2.
 move/disjointP: (forall_inP (forall_inP i1 _ H1) _ (tO_in_action P1 _ H0)).
 move/(_ _ H3); rewrite H2; done.

 destruct p1p2.
 move/setUP: AV2; elim.
 move/setUP; elim; intros.
 move/bigcupP: H0; elim; intros.
 move/disjointP: (forall_inP (forall_inP i0 _ H0) _ (pI_in_action P2)).
 move/(_ _ H2); rewrite H1; done.
 move/bigcupP: H0; elim; intros; move/bigcupP: H1; elim; intros.
 move/disjointP: (forall_inP (forall_inP i0 _ H0) _ (tO_in_action P2 _ H1)).
 move/(_ _ H2); rewrite H3; done.

 move/bigcupP; elim; intros.
 move/bigcupP: H0; elim; intros.
 move/disjointP: (forall_inP (forall_inP i0 _ H0) _ (tH_in_action P2 _ H1)).
 move/(_ _ H3); rewrite H2; done.


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
 rewrite H in Heqnu; done.
 done.
 eapply disabled_r.
 apply Heqmu.
 done.
 rewrite //= /prePIOA_comptrans Heqeta Heqmu in Heqnu.
 apply/contraT; intros.
 rewrite H in Heqnu; done.
 done.
 apply disabled_lr; done.
Qed.

Lemma compPIOA_tr_sym x s : x \in cover (action p1p2) ->
  (tr (comp_prePIOA P1 P2) s x = None <-> (tr (comp_prePIOA P2 P1) (s.2, s.1) x = None)) /\
  (forall mu, tr (comp_prePIOA P1 P2) s x = Some mu -> exists eta, tr (comp_prePIOA P2 P1) (s.2, s.1) x = Some eta /\ 
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
  exists (x0 <- m0; y <- m; ret (x0, y)).
  split.
  done.
  inversion H0; subst.
  rewrite /meas_fmap; dsimp.
  rewrite measBind_swap.
  apply measBind_cong_r; intros.
  rewrite bindAssoc; apply measBind_cong_r; intros.
  rewrite bindRet; reflexivity.
  eapply tr_subDist; symmetry; apply Heqmu.
  eapply tr_subDist; symmetry; apply Heqeta.


  intros.
  have: x \notin cover (action P2).
  destruct (x \notin cover (action P2)); done.

  intro Hx.
  rewrite Hx in H0; inversion H0; subst.
  exists (x0 <- m; ret (s.2, x0)).
  rewrite Hx.
  split.
  done.
  rewrite /meas_fmap.
  rewrite bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet; simpl; reflexivity.
  eapply tr_subDist; symmetry; apply Heqmu.

  intros.
  have: x \notin cover (action P1).
  destruct (x \notin cover (action P1)); done.

  intro Hx.
  rewrite Hx in H0; inversion H0; subst.
  exists (y <- m; ret (y, s.1)).
  rewrite Hx.
  split.
  done.
  rewrite /meas_fmap.
  rewrite bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet; simpl; reflexivity.
  eapply tr_subDist; symmetry; apply Heqeta.

  done.
Qed.

  Lemma compTaskP (t : Task A) :
    reflect (t \in Tasks P1 \/ t \in Tasks P2) (t \in (Tasks p1p2)).
  have: pTO P1 :|: pTO P2 :|: (pTH P1 :|: pTH P2) =
        (pTO P1 :|: pTH P1) :|: (pTO P2 :|: pTH P2).
  rewrite !setUA.
  congr (_ :|: _).
  rewrite -setUA.
  rewrite -setUA.
  congr (_ :|: _).
  rewrite setUC; done.
  intros.
  apply/(iffP idP).
  rewrite /Tasks //=.
  rewrite x.
  move/setUP.
  elim.
  intro; left; done.
  intro; right; done.
  rewrite /Tasks //= x.
  elim.
  intro; apply/setUP; left; done.
  intro; apply/setUP; right; done.
  Qed.

Definition taskInjl (t : Task A) :
  t \in Tasks P1 -> t \in Tasks p1p2.
  rewrite /Tasks //=.
  move/setUP; elim.
  intro; apply/setUP; left; apply/setUP; left; done.
  intro; apply/setUP; right; apply/setUP; left; done.
Defined.

Definition taskInjr (t : Task A) :
  t \in Tasks P2 -> t \in Tasks p1p2.
  rewrite /Tasks //=.
  move/setUP; elim.
  intro; apply/setUP; left; apply/setUP; right; done.
  intro; apply/setUP; right; apply/setUP; right; done.
Defined.

Lemma compat_hidden_disabled (T : Task A) x s:
  T \in (pTH P1) -> x \in T -> ~~ enabled P2 s x.
  intros; apply/contraT; rewrite negbK; intros.

  have HC := actSetValid P2 s x H1.
  destruct p1p2.
  move/setUP: HC; elim.
  move/setUP; elim; intros.

  move/disjointP: (forall_inP (forall_inP H3 _ H) _ (pI_in_action P2)).
  move/(_ _ H0).
  rewrite H5; done.

  move/bigcupP: H5; elim; intros.
  move/disjointP: (forall_inP (forall_inP H3 _ H) _ (tO_in_action P2 _ H5)).
  move/(_ _ H0); rewrite H6; done.

  move/bigcupP; elim; intros.
  move/disjointP: (forall_inP (forall_inP H3 _ H) _ (tH_in_action P2 _ H5)).
  move/(_ _ H0).
  rewrite H6; done.
Qed.  


Lemma enabled_hidden_compE (T : Task A) x s :
  T \in (pTH P1) -> x \in T -> enabled P1 s.1 x =
                             enabled p1p2 s x.
  intros.

  simpl.
  have: tr P2 s.2 x = None.
  remember (tr P2 s.2 x) as eta; destruct eta.
  exfalso; apply/negP. eapply compat_hidden_disabled.
  apply H.
  apply H0.
  instantiate (1 := s.2); rewrite /enabled -Heqeta //=.
  done.
  intros.
  rewrite /enabled //= /prePIOA_comptrans.
  rewrite x0.
  have: x \notin cover (action P2).
  destruct p1p2.
  apply/contraT; rewrite negbK; intros.
  move/bigcupP: H4; elim; intros.
  move/disjointP: (forall_inP (forall_inP H2 _ H) _ H4).
  move/(_ _ H0).
  rewrite H5; done.
  intro.
  rewrite x1.
  destruct (tr P1 s.1 x); done.
Qed.

Context (p2p1 : P2 ||| P1).

Lemma compPIOA_pI_sym :
  pI p1p2 = pI p2p1.
  simpl.
  rewrite (setUC (pI P1) (pI P2)).
  rewrite (setUC (pTO P1) (pTO P2)).
  done.
Qed.

Lemma compPIOA_pTO_sym :
  pTO p1p2 = pTO p2p1.
  by rewrite //= setUC.
Qed.

Lemma compPIOA_pTH_sym :
  pTH p1p2 = pTH p2p1.
  by rewrite //= setUC.
Qed.

Lemma compPIOA_enabled_sym s x :
  enabled p1p2 s x = enabled p2p1 (s.2, s.1) x.
rewrite /enabled //= /prePIOA_comptrans.
remember (tr P1 s.1 x) as mu; remember (tr P2 s.2 x) as eta; destruct mu; destruct eta; rewrite -Heqmu -Heqeta.
done.
caseOn (x \in cover (action P2)); intro Hc; rewrite Hc; done.
caseOn (x \in cover (action P1)); intro Hc; rewrite Hc; done.
done.
Qed.


Definition compPIOA_appTask_sym T mu : isSubdist mu ->
  T \in Tasks p1p2 ->
  appTask p1p2 T mu ~~
  meas_fmap (appTask p2p1 T (x <- mu; ret ((x.1.2, x.1.1), x.2))) (fun x => ((x.1.2, x.1.1), x.2)) @ 0.
  intros Hsubmu HTin.
  intros.
  rewrite /appTask.
  rewrite /meas_fmap.
  rewrite !bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet; simpl.
  rewrite /runTask.
  have:  [pick x0 in T  | enabled p1p2 x.1 x0] =
         [pick x0 in T  | enabled p2p1 (x.1.2, x.1.1) x0].  
  
  {
    apply eq_pick.
    move=> z.
    simpl.
    rewrite compPIOA_enabled_sym.
    done.
  }


  intros.
  rewrite -x0.
  case: pickP; intros.

  destruct (compPIOA_tr_sym x1 x.1).

  apply/bigcupP.
  exists T.

  rewrite /action.
  rewrite /Tasks in HTin.
  move/setUP: HTin; elim; intro.
  apply/setUP; left; apply/setUP; right; done.
  apply/setUP; right; done.
  move/andP: i; elim; done.


  remember (tr p1p2 x.1 x1) as D; destruct D; symmetry in HeqD.

  destruct (H1 _ HeqD).
  destruct H2.
  rewrite H2.
  rewrite HeqD.
  simpl.
  rewrite (measBind_cong_l H3).
  rewrite /meas_fmap.
  rewrite !bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet.
  rewrite /external.
  rewrite compPIOA_pI_sym compPIOA_pTO_sym.

  destruct (x1 \in pI p2p1 :|: cover (pTO p2p1)).
  rewrite bindRet; simpl; reflexivity.
  rewrite bindRet; simpl; reflexivity.

  eapply (@tr_subDist _ p2p1 _ _ x2).
  apply H2.
  intros; destruct (x1 \in external p1p2); dsubdist.
  rewrite HeqD.
  destruct H0.
  rewrite (H0 HeqD).
  rewrite bindRet; simpl.
  destruct x; simpl.
  destruct s; simpl.
  reflexivity.
  rewrite bindRet; simpl; destruct x; simpl.
  destruct s; simpl; reflexivity.

  done.
Qed.
  
End compPIOAProps.

Section CompPIOA_symm.
  Context {A : finType}.
  Context (P1 P2 : @PIOA A).
  Context (p1p2 : P1 ||| P2).
  Definition p2p1 := compatible_sym P1 P2 p1p2.
          
  Context (ic : inputClosed p1p2).

  Lemma inputClosed_sym : inputClosed p2p1.
    rewrite /inputClosed.
    rewrite -compPIOA_pI_sym; done.
  Qed.

  Lemma compPIOA_sym : @refinement _ p1p2 p2p1 ic inputClosed_sym 0.
    eapply stateSimSound.
    instantiate (1 := fun p => (p.2, p.1)).
    constructor.
    done.
    intros.
    exists (T :: nil).
    split.
    simpl.
    apply/andP; split.
    apply/compTaskP.
    move/compTaskP: H.
    elim.
    intro; right; done.
    intro; left; done.
    done.
    simpl.

    Check compPIOA_appTask_sym.
    
    symmetry.
    eapply compPIOA_appTask_sym.

    apply compTaskP in H.
    rewrite/ isTask.
    rewrite /Tasks.

    split.
    rewrite -compTaskP in H.
    
    admit.
  Admitted.
End CompPIOA_symm.
End compPIOAProps.

Section CompPIOA_assoc.
  Context {A : finType}.
  Context (P1 P2 P3 : @PIOA A).
  Context (p2p3 : P2 ||| P3).
  Context (p1_p2p3 : P1 ||| p2p3).
  Context (p1p2 : P1 ||| P2).
  Context (p1p2_p3 : p1p2 ||| P3).
  Context (ic : inputClosed p1p2_p3).

  Lemma pI_comp_assoc : pI p1p2_p3 = pI p1_p2p3.
    simpl.
    admit.
  Admitted.

  Lemma inputClosed_assoc : inputClosed p1_p2p3.
    rewrite /inputClosed.
    rewrite -pI_comp_assoc.
    apply ic.
  Qed.

  Lemma compPIOA_assoc : @refinement _ p1_p2p3 p1p2_p3 inputClosed_assoc ic 0.
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