

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum Refinement Action Closure CompPIOA.




Lemma closure_eq_l {A B : choiceType} (R : {meas A} -> {meas B} -> bool) mu eta mu' :
  mu = mu' ->
  closure R mu' eta ->
  closure R mu eta.
  intro; subst; done.
Qed.

Lemma closure_eq_r {A B : choiceType} (R : {meas A} -> {meas B} -> bool) mu eta eta' :
  eta = eta' ->
  closure R mu eta' ->
  closure R mu eta.
  intro; subst; done.
Qed.


Section SameHiddenParaSim.
  
  Context {G D : ctx}.
  Context (P1 : PIOA G D).
  Context (P2 : PIOA G D).
  Context (R : {meas (St P1) * trace P1} -> {meas (St P2) * trace P2} -> bool).

  Record ShSim :=
    {
      sh_tr : forall mu eta, mvalid P1 mu -> mvalid P2 eta -> R mu eta -> exists S S' t, [/\ mu = S ** ret t & eta = S' ** ret t];
      sh_start : R (initDist P1) (initDist P2);
      sh_v : forall c mu eta,
          mvalid P1 mu ->
          mvalid P2 eta ->
          R mu eta ->
          c \in outputs P1 ->
          closure R (act P1 (inr c) mu) (act P2 (inr c) eta);
      sh_h: forall h mu eta,
          mvalid P1 mu ->
          mvalid P2 eta ->
          R mu eta ->
          closure R (act P1 (inl h) mu) (act P2 (inl h) eta);
      sh_i : forall a mu eta,
          mvalid P1 mu ->
          mvalid P2 eta ->
          R mu eta ->
          tag a \in inputs P1 ->
          closure R (act_i P1 a mu) (act_i P2 a eta)
                    }.

  Theorem shSim_Internal : closed P1 -> ShSim -> InternalSim P1 P2 (fun c => (nil, c, nil)) (fun h => (h :: nil)) R .
    move => Hclosed; case => h1 h2 h3 h4 h5.
    constructor.
    intros.

    destruct (h1 mu eta H H0).
    done.
    destruct H2 as [S' [t [H3 H4]]]; subst.
    msimp.
    rewrite !mbind_unused.
    elim H => _ Hm1.
    elim H0 => _ Hm2.
        rewrite /isdist !mass_mprod !mass_ret !pmulr1 in Hm1, Hm2.
        rewrite (eqP Hm1) (eqP Hm2) !mscale_1 //=.
    
    done.
    simpl; intros; apply h3; done.
    simpl; intros; apply h4; done.
Qed.

End SameHiddenParaSim.


Definition filter_tr {G D : ctx} (P : PIOA G D) (t : trace P) : trace P:=
  filter (fun x => tag x \in inputs P ++ outputs P) t.

Lemma filter_tr_eq {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') :
  comparable P P' ->
  filter_tr P =1 filter_tr P'.
  move/andP; elim => h1 h2.
  move => x; rewrite /filter_tr.
  apply eq_filter => t; simpl.
  rewrite !mem_cat.
  rewrite (seq_eqmemP _ _ h1) (seq_eqmemP _ _ h2) //=.
Qed.

Lemma act_v_filter_tr {G D : ctx} (P : PIOA G D) S t c :
  c \in outputs P -> 
  act P (inr c) (S ** ret t) =
  (p <- act P (inr c) (S ** ret (filter_tr P t));
     match ocons_ohead p.2 (filter_tr P t) with
       | Some a => ret (p.1, a :: t)
       | None => ret (p.1, t)
                     end).
  move => Hc.
  rewrite /act 3!mbindA; apply mbind_eqP => s Hs; msimp.
  case: (app_vP P c s Hc).
  move => m mu Htr ->; msimp.
  rewrite ocons_ohead_cons.
  done.
  move => H ->; msimp; rewrite ocons_ohead_tt.
  done.
Qed.

Lemma act_h_filter_tr {G D : ctx} (P : PIOA G D) S t h :
  act P (inl h) (S ** ret t) =
  (p <- act P (inl h) (S ** ret (filter_tr P t));
   ret (p.1, t)).
  rewrite /act 3!mbindA; apply mbind_eqP => s Hs; msimp.
  case: (app_hP P h s).
  move => m mu _ ->; msimp; done.
  move => _ ->; done.
Qed.

Lemma act_i_filter_tr {G D : ctx} (P : PIOA G D) S t a :
  act_i P a (S ** ret t) =
  (p <- act_i P a (S ** ret (filter_tr P t)); ret (p.1, a :: t)).
  rewrite /act_i; msimp; done.
Qed.
  

Lemma filter_tr_valid {G D : ctx} (P : PIOA G D) t :
  valid_trace P (filter_tr P t).
  induction t.
  done.
  simpl.
  caseOn (tag a \in inputs P ++ outputs P) => H.
  rewrite H.
  simpl.
  rewrite H IHt //=.
  rewrite (negbTE H) IHt //=.
Qed.

Lemma mvalid_constant_r {G D : ctx} (P: PIOA G D) S t :
  valid_trace P t ->
  isdist S ->
  mvalid P (S ** ret t).
  intros; split.
  move => x; move/support_bindP; elim => s; elim => Hs; msimp; rewrite in_ret; move/eqP => ->.
  done.
  rewrite /isdist mass_mprod mass_ret pmulr1 (eqP H0); done.
Qed.

Lemma indist_act_v_mvalid {G D : ctx} (P : PIOA G D) S t mu c :
  c \in outputs P ->
  valid_trace P t ->
  (forall x, x \in support mu -> x \in support (act P (inr c) (S ** ret t))) ->
  isdist mu ->
  mvalid P mu.
    move => Hc Ht H Hmu.
  split.
  move => x Hx; move: (H _ Hx).
  move/support_bindP; elim => p; elim => Hp.
  move/support_bindP: Hp; elim => s; elim => Hs; msimp; rewrite in_ret; move/eqP => ->; simpl.
  case: (app_vP P c s Hc).
  move => m eta _ ->.
  msimp.
  move/support_bindP; elim => X; elim => HX; rewrite in_ret; move/eqP => ->; simpl.
  rewrite mem_cat Hc orbT Ht //=.
  move => _ ->; msimp; rewrite in_ret; move/eqP => ->; simpl; done.
  done.
Qed.

Lemma indist_act_v_trP {G D : ctx} (P : PIOA G D) S t mu c :
  c \in outputs P ->
  valid_trace P t ->
  (forall x, x \in support mu -> x \in support (act P (inr c) (S ** ret t))) ->
  forall x, x \in support mu -> (x.2 = t \/ (exists a, [/\ tag a = c & x.2 = a :: t])).
  intros.
  move: (H1 _ H2).
  move/support_bindP; elim => p; elim => Hp.
  move/support_bindP: Hp; elim => s; elim => Hs; msimp; rewrite in_ret; move/eqP => ->; simpl.
  case: (app_vP P c s H).
  move => m eta _ ->.
  msimp; move/support_bindP; elim => s'; elim => Hs'.
  rewrite in_ret; move/eqP => ->; right.
  exists (mkact G c m); split; done.
  move => _ ->; msimp; rewrite in_ret; move/eqP => ->; left; done.
Qed.

Lemma indist_act_h_mvalid {G D : ctx} (P : PIOA G D) S t mu h :
  valid_trace P t ->
  (forall x, x \in support mu -> x \in support (act P (inl h) (S ** ret t))) ->
  isdist mu ->
  mvalid P mu.
    move => Ht H Hmu.
  split.
  move => x Hx; move: (H _ Hx).
  move/support_bindP; elim => p; elim => Hp.
  move/support_bindP: Hp; elim => s; elim => Hs; msimp; rewrite in_ret; move/eqP => ->; simpl.
  case: (app_hP P h s).
  move => m eta _ ->.
  msimp.
  move/support_bindP; elim => X; elim => HX; rewrite in_ret; move/eqP => ->; simpl; done.
  move => _ ->; msimp; rewrite in_ret; move/eqP => ->; simpl; done.
  done.
Qed.

Lemma indist_act_h_trP {G D : ctx} (P : PIOA G D) S t mu h :
  valid_trace P t ->
  (forall x, x \in support mu -> x \in support (act P (inl h) (S ** ret t))) ->
  forall x, x \in support mu -> x.2 = t.
  intros.
  move: (H0 _ H1).
  move/support_bindP; elim => p; elim => Hp.
  move/support_bindP: Hp; elim => s; elim => Hs; msimp; rewrite in_ret; move/eqP => ->; simpl.
  case: (app_hP P h s).
  move => m mu0 _ ->.
  move/support_bindP; elim => s'; elim => Hs'.
  rewrite in_ret; move/eqP => ->; done.
  move => _ ->; msimp; rewrite in_ret; move/eqP => ->; done.
Qed.

Definition extension {G D D' : ctx} (P P' : PIOA G D) (E : PIOA G D') (R : {meas (St P * trace P)} -> {meas St P' * trace P'} -> bool) := fun (mu : {meas St (P ||| E) * trace P}) (eta : {meas St (P' ||| E) * trace P'}) =>
  [&&
     all (fun p => all (fun p' => [&& p.1.2 == p'.1.2 & p.2 == p'.2]) (support eta)) (support mu) &
     R (mu <$> fun p => (p.1.1, filter_tr P p.2)) (eta <$> fun p => (p.1.1, filter_tr P' p.2))].

Lemma mass_mprod {A B : choiceType} (m : {meas A}) (m' : {meas B}) :
  mass (m ** m') = mass m * mass m'.
  rewrite mass_bindE.
  have -> : Premeas.integ m (fun x : A => mass (m' <$> pair x)) =
            Premeas.integ m (fun _ => mass m').
  apply integ_eq_fun => x Hx.
  rewrite mass_fmap //=.
  rewrite /Premeas.integ.
  rewrite -big_distrl //=.
  rewrite /mass /Premeas.integ.
  have -> : \big[padd/0]_(p <- _pmeas m) (p.1 * 1) =
            \big[padd/0]_(p <- _pmeas m) (p.1).
  apply eq_big; rewrite //=.
  intros; rewrite pmulr1 //=.
  done.
Qed.

Lemma extensionP {G D D' : ctx} (P P' : PIOA G D) (E : PIOA G D') (R : _ -> _ -> bool) mu eta :
  isdist mu -> isdist eta -> reflect (exists S S' e t,
              [/\ isdist S, isdist S', mu = (S ** ret e) ** ret t,
               eta = (S' ** ret e) ** ret t &
               R (S ** ret (filter_tr P t)) (S' ** ret (filter_tr P' t))]) (extension P P' E R mu eta).
  simpl in * => Hmu Heta.
  apply/(iffP idP).
  move/andP; elim => H1 H2; simpl in *.
  have: all (fun p => all (fun p' => p.2 == p'.2) (support eta)) (support mu).
    apply/all2P => x Hx y Hy; elim (andP (all2P _ _ _ H1 x Hx y Hy)); done.
    simpl.
  move => H.
  move/constant_rP: H.
  move/(_ nil); rewrite (eqP Hmu) (eqP Heta); move/(_ is_true_true is_true_true).

  elim=> S; elim => S'; elim => x; elim => heq1 heq2; subst.

  have: all (fun p => all (fun p' => p.2 == p'.2) (support S)) (support S').
    apply/all2P => a Ha y Hy.
    move/allP: H1.
    move/(_ (y, x)).
    have -> : (y,x) \in support (S ** ret x).
        apply/support_bindP; exists y; split; rewrite //=.
        msimp; rewrite in_ret //=.
    move/(_ is_true_true).
    move/allP.
    move/(_ (a, x)).
    have -> : (a,x) \in support (S' ** ret x).
        apply/support_bindP; exists a; split; rewrite //=.
        msimp; rewrite in_ret //=.
    move/(_ is_true_true).
    move/andP; simpl; elim; rewrite eq_sym; done.

  move/constant_rP.
  move/(_ (start E)).
  rewrite /isdist !mass_mprod !mass_ret !pmulr1 in Hmu, Heta.
  rewrite (eqP Hmu) (eqP Heta); move/(_ is_true_true is_true_true).
  elim => S1; elim => S1'; elim => e; elim; intros; subst.
  exists S1'.
  exists S1.
  exists e.
  exists x; split.
  rewrite mass_mprod mass_ret pmulr1 in Hmu; done.
  rewrite mass_mprod mass_ret pmulr1 in Heta; done.
  done.
  done.

  have <- : (x <- (S1' ** (ret e)) ** (ret x); ret (x.1.1, filter_tr P x.2)) = (S1' ** ret filter_tr P x) by msimp.
  have <- : (x <- (S1 ** (ret e)) ** (ret x); ret (x.1.1, filter_tr P' x.2)) = (S1 ** ret filter_tr P' x) by msimp.
  done.

  elim => S; elim => S'; elim => e; elim => t; elim; intros; subst.
  apply/andP; split.
  apply/allP => x; move/support_bindP; elim => X; elim => HX.
  msimp; rewrite in_ret; move/eqP => heq; subst.
  move/support_bindP: HX; elim => X'; elim => HX'; msimp; rewrite in_ret; move/eqP => heq; subst.
  apply/allP => y; move/support_bindP; elim => Y; elim => HY.
  msimp; rewrite in_ret; move/eqP => heq; subst.
  simpl; rewrite !eq_refl //=.

  have -> : (x <- (S ** (ret e)) ** (ret t); ret (x.1.1, filter_tr P x.2)) = (S ** ret filter_tr P t) by msimp.
  have -> : (x <- (S' ** (ret e)) ** (ret t); ret (x.1.1, filter_tr P' x.2)) = (S' ** ret filter_tr P' t) by msimp.
  done.
Qed.  

Lemma support_act_decomp_tr {G D : ctx} (P : PIOA G D) c S t xt :
  c \in outputs P ->
  xt \in support (act P (inr c) (S ** ret t)) ->
  (xt.2 = t \/ (exists a, tag a = c /\ xt.2 = a :: t)).
  move => Hc; move/support_bindP; elim => mu; elim=> Hmu.
  move/support_bindP: Hmu.
  elim => p; elim => Hp.
  msimp; rewrite in_ret; move/eqP => heq; subst.
  simpl.

  case: (app_vP P c p Hc).
  move => m eta _ ->.
  msimp; move/support_bindP; elim => a; elim => Ha.
  rewrite in_ret; move/eqP => ->; right.
  exists (mkact G c m); split.
  done.
  done.
  move => _ ->; msimp; rewrite in_ret; move/eqP => ->.
  left; done.
Qed.

Lemma support_mprod_ret {A B : choiceType} (x : A) (m : {meas A}) (b : B) :
  (x \in support m) = ((x,b) \in support (m ** ret b)).
  apply Bool.eq_true_iff_eq; split.
  intros; apply/support_bindP; exists x; split; msimp; [done | rewrite in_ret //=].
  move/support_bindP; elim => a; elim => Ha; msimp; rewrite in_ret.
  rewrite /eq_op //=; move/andP; elim; move/eqP => -> _; done.
Qed.

  

Theorem shSim_comp {G D D' : ctx} (P  P' : PIOA G D) (E : PIOA G D') (R : _ -> _ -> bool) (He : env P E) (Hcomp : comparable P P') :
  ShSim P P' R -> ShSim (P ||| E) (P' ||| E) (extension P P' E R).

  case => h1 h2 h3 h4 h5; constructor.
  move => mu eta Hmu Heta; move/extensionP.
  rewrite /isdist (eqP (proj2 Hmu)) (eqP (proj2 Heta)); move/(_ is_true_true is_true_true).
  
  elim => S; elim => S'; elim => e; elim => t; elim => _ heq1 heq2; subst => HR.
  exists (S ** ret e); exists (S' ** ret e); exists t; done.


  rewrite /initDist //=; apply/extensionP.
  apply isdist_ret.
  apply isdist_ret.
  exists (ret start P); exists (ret start P'); exists (start E); exists nil; split.
  apply isdist_ret.
  apply isdist_ret.
  msimp; done.
  msimp; done.
  msimp; apply h2.

  move => c mu eta [Hmu1 Hmu2] [Heta1 Heta2]. 
  move/extensionP; rewrite /isdist (eqP Hmu2) (eqP Heta2); move/(_ is_true_true is_true_true). 
  elim => S; elim=> S'; elim=> e; elim=> t; elim => HS HS' heq1 heq2 HR Hc; subst.

  move/andP: He; elim => Hcompat Hclosed.
  have Hcompat' : compatible P' E.
    apply/seq_disjointP => x; move/andP: Hcomp; elim => _ /seq_eqmemP => <-.
    move: (seq_disjointP _  _ Hcompat x); done.
  have Hclosed' : closed (P' ||| E).
    rewrite /closed //=.
    apply/seqD_eqnil => x; rewrite !mem_cat.
    move/andP: Hcomp; elim => /seq_eqmemP <- /seq_eqmemP <-.
    move: (seqD_eqnil _ _ Hclosed x); rewrite !mem_cat //=.

  simpl in Hc; rewrite mem_cat in Hc; move/orP: Hc; elim => [HcoP | HcoE].
  have HcoP': c \in outputs P'.
    move/andP: Hcomp; elim => _ /seq_eqmemP => <-; done.

  have HR' := HR.
  move/h3: HR'.
  move/(_ c).

  have Hmu' : mvalid P (S ** ret filter_tr P t).
    apply mvalid_constant_r.
    apply filter_tr_valid.
    rewrite /isdist //=.
  move/(_ Hmu') {Hmu'}.
  have Heta' : mvalid P' (S' **  (ret filter_tr P' t)).
    apply mvalid_constant_r.
    apply filter_tr_valid.
    rewrite /isdist //=.
  move/(_ Heta') {Heta'}.
  move/(_ HcoP).

  elim => L; move/and3P; elim => HL1 HL2 HL3; simpl in L, HL3.

  have HL: forall p, p \in support L ->
                        exists S S' t',
                          [/\ p.1 = S ** ret t',
                                p.2 = S' ** ret t',
                                ([/\ R p.1 p.2, isdist S & isdist S']) &
                              (t' = filter_tr P t \/ exists a, (tag a = c /\ t' = a :: filter_tr P t))].
    move => p Hp.
    move/and3P: (allP HL3 _ Hp); elim => Hp1 Hp2 Hp3.
    have Hp3' := Hp3.
    move/h1: Hp3'.
    have Hm1: mvalid P p.1.
        eapply indist_act_v_mvalid.
        apply HcoP.
        apply (filter_tr_valid P t).
        move => x Hx.
        instantiate (1 := S).
        rewrite (eqP HL1).
        apply/support_bindP.
        exists p; split; done.
        done.
    move/(_ Hm1) {Hm1}.
    have Hm1: mvalid P' p.2.
        eapply indist_act_v_mvalid.
        apply HcoP'.
        apply (filter_tr_valid P' t).
        move => x Hx.
        instantiate (1 := S').
        rewrite (eqP HL2).
        apply/support_bindP.
        exists p; split; done.
        done.
    move/(_ Hm1) {Hm1}.

    elim => S0'; elim => S1'; elim => t'; elim => heq1 heq2.
    exists S0'; exists S1'; exists t'; split.
    done.
    done.
    split.
    done.
    rewrite /isdist.
    have -> : mass S0' = mass p.1 by rewrite heq1 mass_mprod mass_ret pmulr1 //=.
    rewrite (eqP Hp1) //=.
    rewrite /isdist.
    have -> : mass S1' = mass p.2 by rewrite heq2 mass_mprod mass_ret pmulr1 //=.
    rewrite (eqP Hp2) //=.

    move: (indist_act_v_trP P S (filter_tr P t) p.1).
    move/(_ c HcoP).
    move/(_ (filter_tr_valid _ _)).
    rewrite (eqP HL1).
    have Htmp : forall x, x \in support p.1 -> x \in support (p0 <- L; p0.1).
        intros; apply/support_bindP.
        exists p; split; done.
    move/(_ Htmp) {Htmp}.
    move => H.
    have: mass S0' != 0.
    have -> : mass S0' = mass p.1 by rewrite heq1 mass_mprod mass_ret pmulr1 //=.
    rewrite (eqP Hp1) //=.
    move/mass_neq0; elim => s Hs.
    move: (H (s, t')).
    rewrite heq1.
    simpl.
    rewrite -support_mprod_ret.
    move/(_ Hs).
    done.
  
  caseOn (c \in inputs E) => [HciE | HcniE].


  (* ******          c in inputs E           ******* *)
  rewrite act_v_comp_decomp_l_int; [idtac | done | done | done].
  rewrite act_v_comp_decomp_l_int; [idtac | done | done | done].
  rewrite act_v_filter_tr; last by done.
  rewrite (act_v_filter_tr P'); last by done.
  rewrite (eqP HL1) (eqP HL2); rewrite !mbindA.
  apply closure_bind => p Hp; simpl in p.
  move: (HL _ Hp); elim => S0; elim => S1; elim => t'; elim => heq1 heq2; elim => Hp1 Hp2 Hp3.
  elim => Ht'.

  rewrite heq1 heq2; msimp.
  rewrite Ht' -(filter_tr_eq P P').
  rewrite !ocons_ohead_tt; msimp.
  rewrite !ocons_ohead_tt; msimp.
  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists S0; exists S1; exists e; exists t; split.
  done.
  done.
  msimp; done.
  msimp; done.
  rewrite -(filter_tr_eq P P'); last by done.
  rewrite -!Ht' -heq1 -heq2; done.
  done.

  destruct Ht' as [a [Ha1 Ha2]].
  rewrite heq1 heq2; msimp.
  rewrite Ha2 ocons_ohead_cons; msimp.
  rewrite (filter_tr_eq P P'). 
  rewrite ocons_ohead_cons.
  rewrite ocons_ohead_cons.
  msimp.
  rewrite ocons_ohead_cons.
  rewrite (mbind_swap S0) (mbind_swap S1); apply closure_bind => e' He'.
  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists S0; exists S1; exists e'; eexists; split.
  done.
  done.
  msimp; done.
  msimp; done.
  simpl.
  rewrite !mem_cat Ha1 HcoP HcoP' !orbT -(filter_tr_eq P P').
  rewrite -Ha2 -heq1 -heq2; done.
  done.
  done.



  (* *******       c notin inputs E       ******  *)
  rewrite act_v_comp_decomp_l_ext; [idtac | done | done | done].
  rewrite act_v_comp_decomp_l_ext; [idtac | done | done | done].

  rewrite act_v_filter_tr; last by done.
  rewrite (act_v_filter_tr P'); last by done.
  rewrite 2!mbindA.
  rewrite (eqP HL1) (eqP HL2); msimp.
  apply closure_bind => p Hp.
  move: (HL _ Hp); elim => S0; elim => S1; elim => t'; elim => heq1 heq2; elim => Hp1 Hp2 Hp3 {HL}.
  elim => Ht'.
  rewrite heq1 heq2; msimp; rewrite Ht'.
  rewrite ocons_ohead_tt.
  rewrite -(filter_tr_eq P P'); last by done.
  rewrite ocons_ohead_tt.
  msimp.
  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists S0; exists S1; eexists; eexists; split.
  done.
  done.
  msimp; done.
  msimp; done.
  rewrite -(filter_tr_eq P P'); last by done.
  rewrite -Ht' -heq1 -heq2; done.

  destruct Ht' as [a [Ha1 Ha2]].
  rewrite heq1 heq2; msimp.
  rewrite Ha2 (filter_tr_eq P P'); last by done.
  rewrite !ocons_ohead_cons.
  msimp; apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists S0; exists S1; eexists; eexists; split.
  done.
  done.
  msimp; done.
  msimp; done.
  rewrite -(filter_tr_eq P P'); last by done.
  simpl; rewrite !mem_cat Ha1 HcoP !orbT -Ha2 -heq1 -heq2; done.



  (* ******     c in outputs E ******  *)
  caseOn (c \in inputs P) => [HciP | HcniP].


  (* c in inputs P *)

  have HciP': c \in inputs P'.
    move/andP: Hcomp; elim; move/seq_eqmemP => <-; done.

  rewrite act_v_comp_decomp_r_int; [idtac | done | done | done].
  rewrite act_v_comp_decomp_r_int; [idtac | done | done | done].

  rewrite (mbind_swap S) (mbind_swap S').
  apply closure_bind => xt Hxt.

  have Hxt' := Hxt.
  move/support_act_decomp_tr: Hxt'.
  move/(_ HcoE).
  elim.
  move => heq; rewrite heq.
  rewrite ocons_ohead_tt.
  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists S; exists S'; eexists; eexists.
  split.
  done.
  done.
  msimp; done.
  msimp; done.
  done.
  elim => a; elim => Ha1 Ha2.
  rewrite Ha2 ocons_ohead_cons.

  have HR' := HR.
  move/h5: HR'.
  move/(_ a).
  have: mvalid P (S ** (ret filter_tr P t)).
     split.
     move => x; move/support_bindP; elim => s; elim => Hs; msimp; rewrite in_ret; move/eqP => ->; apply filter_tr_valid.
     rewrite /isdist mass_mprod mass_ret pmulr1 (eqP HS) //=.
  move => Htmp; move/(_ Htmp) {Htmp}.
  have: mvalid P' (S' ** (ret filter_tr P' t)).
     split.
     move => x; move/support_bindP; elim => s; elim => Hs; msimp; rewrite in_ret; move/eqP => ->; apply filter_tr_valid.
     rewrite /isdist mass_mprod mass_ret pmulr1 (eqP HS') //=.
  move => Htmp; move/(_ Htmp) {Htmp}.
  rewrite Ha1; move/(_ HciP).
  elim => l. move/and3P; elim => Hl1 Hl2 Hl3.


  have -> :
    (x <- S; s' <- app_i P a x; ret (s', xt.1, a :: t)) =
    (pp <- (p <- l; p.1); ret (pp.1, xt.1, a :: t)).
    rewrite -(eqP Hl1); msimp; done.

  have -> :
    (x <- S'; s' <- app_i P' a x; ret (s', xt.1, a :: t)) =
    (pp <- (p <- l; p.2); ret (pp.1, xt.1, a :: t)).
    rewrite -(eqP Hl2); msimp; done.

  msimp; apply closure_bind => p Hp.
  move/and3P: (allP Hl3 _ Hp); elim => Hp1 Hp2 Hp3.
  
  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists (p.1 <$> fst).
  exists (p.2 <$> fst).
  exists xt.1.
  exists (a :: t); split.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  msimp; done.
  msimp; done.
  msimp.
  rewrite !mem_cat Ha1 HciP HciP' !orTb.
  unfold act_i in *.
  have Hp11: forall x, x \in support p.1 -> x.2 = a :: filter_tr P t.
    intros; have: x \in support (p <- l; p.1).
    apply/support_bindP; exists p; split; done.
    rewrite -(eqP Hl1).
    msimp.
    move/support_bindP; elim => s'; elim => _.
    move/support_bindP; elim => s''; elim => _.
    rewrite in_ret; move/eqP => -> //=.
  have Hp12: forall x, x \in support p.2 -> x.2 = a :: filter_tr P t.
    intros; have: x \in support (p <- l; p.2).
    apply/support_bindP; exists p; split; done.
    rewrite -(eqP Hl2).
    msimp.
    move/support_bindP; elim => s'; elim => _.
    move/support_bindP; elim => s''; elim => _.
    rewrite in_ret; move/eqP => -> //=.
    rewrite (filter_tr_eq P P'); last by done; done.
    done.
  have -> : (x <- p.1; ret (x.1, a :: filter_tr P t)) = p.1.
    rewrite -(bind_ret p.1); rewrite mbindA; apply mbind_eqP => x Hx.
    msimp.
    rewrite -(Hp11 _ Hx); destruct x; done.
  have -> : (x <- p.2; ret (x.1, a :: filter_tr P' t)) = p.2.
    rewrite -(bind_ret p.2); rewrite mbindA; apply mbind_eqP => x Hx.
    msimp.
    rewrite -(filter_tr_eq P P'); last by done.
    rewrite -(Hp12 _ Hx); destruct x; done.
  done.



  (* ********* c notin inputs P  **********  *)
  have HcniP' : c \notin inputs P'.
    move/andP: Hcomp; elim; move/seq_eqmemP => <-; done.
  rewrite act_v_comp_decomp_r_ext; [idtac | done | done | done].
  rewrite act_v_comp_decomp_r_ext; [idtac | done | done | done].
  rewrite (mbind_swap S) (mbind_swap S').
  apply closure_bind => xt Hxt.
  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists S; exists S'; eexists; eexists.
  split.
  done.
  done.
  msimp; done.
  msimp; done.
  move/support_act_decomp_tr: Hxt.
  move/(_ HcoE).
  elim.
  move => ->.
  done.
  elim => a; elim => Ha1 Ha2; rewrite Ha2.
  simpl.
  rewrite !mem_cat //=.
  rewrite Ha1.
  rewrite (negbTE HcniP) (negbTE HcniP').
  have HcnoP : c \notin outputs P.
    move: Hcompat; rewrite /compatible.
    rewrite seq_disjoint_sym.
    move/seq_disjointP.
    move/(_ c HcoE); done.
  have HcnoP' : c \notin outputs P'.
    move/andP: Hcomp; elim => _ /seq_eqmemP => <-; done.
  rewrite (negbTE HcnoP) (negbTE HcnoP') //=.



  (* *****   hiddens     ******   *)

  case => h mu eta [Hmu1 Hmu2] [Heta1 Heta2].
  move/extensionP.
  move/(_ Hmu2 Heta2).
  elim => S; elim => S'; elim => e; elim => t; elim => HS HS' heq1 heq2 HR; subst.
  rewrite !act_h_decomp_l.
  rewrite act_h_filter_tr (act_h_filter_tr P'); rewrite 2!mbindA.
  move/h4: HR.
  move/(_ h).
  have Htmp: mvalid P (S ** (ret filter_tr P t)).
    split.
    move => x; move/support_bindP; elim => s; elim => _; msimp; rewrite in_ret; move/eqP => ->; apply filter_tr_valid.
    apply isdist_bind.
    done.
    intros; msimp; apply isdist_ret.
  move/(_ Htmp) {Htmp}.
  have Htmp: mvalid P' (S' ** (ret filter_tr P' t)).
    split.
    move => x; move/support_bindP; elim => s; elim => _; msimp; rewrite in_ret; move/eqP => ->; apply filter_tr_valid.
    apply isdist_bind.
    done.
    intros; msimp; apply isdist_ret.
  move/(_ Htmp) {Htmp}.
  elim => l; move/and3P; elim => Hl1 Hl2 Hl3.
   rewrite (eqP Hl1) (eqP Hl2); rewrite 2!mbindA; apply closure_bind => p Hp.
   msimp.
  move/and3P: (allP Hl3 _ Hp); elim => Hp1 Hp2 Hp3.
   apply id_closure.
   rewrite isdist_fmap //=.
   rewrite isdist_fmap //=.
   apply/extensionP.
   rewrite isdist_fmap //=.
   rewrite isdist_fmap //=.
   exists (p.1 <$> fst).
   exists (p.2 <$> fst).
   exists e.
   exists t.
   split.
   rewrite isdist_fmap //=.
   rewrite isdist_fmap //=.
   msimp; done.
   msimp; done.
   msimp.

   have Hp11 : forall x, x \in support p.1 -> x.2 = filter_tr P t.
    intros; have: x \in support (p <- l; p.1).
    apply/support_bindP; exists p; split; done.
    rewrite -(eqP Hl1); simpl.
    msimp.
    move/support_bindP; elim => s'; elim => _.
    move/support_bindP; elim => s''; elim => _.
    rewrite in_ret; move/eqP => -> //=.
   have Hp12 : forall x, x \in support p.2 -> x.2 = filter_tr P t.
    intros; have: x \in support (p <- l; p.2).
    apply/support_bindP; exists p; split; done.
    rewrite -(eqP Hl2); simpl.
    msimp.
    move/support_bindP; elim => s'; elim => _.
    move/support_bindP; elim => s''; elim => _.
    rewrite in_ret; move/eqP => -> //=.
    rewrite (filter_tr_eq P P'); last by done.
    done.
   have -> : (x <- p.1; ret (x.1, filter_tr P t)) = p.1.
    rewrite -(bind_ret p.1); rewrite mbindA; apply mbind_eqP => x Hx.
    msimp; rewrite -(Hp11 _ Hx); destruct x; done.
   have -> : (x <- p.2; ret (x.1, filter_tr P' t)) = p.2.
    rewrite -(bind_ret p.2); rewrite mbindA; apply mbind_eqP => x Hx.
    rewrite -(filter_tr_eq P P'); last by done.
    msimp; rewrite -(Hp12 _ Hx); destruct x; done.
   done.

   move/extensionP.
   move/(_ Hmu2 Heta2); elim => S; elim => S'; elim => e; elim => t; elim => HS HS' heq1 heq2 HR; subst.
   rewrite !act_h_decomp_r.
   rewrite (mbind_swap S) (mbind_swap S'); apply closure_bind => xt Hxt.
   apply id_closure.
   rewrite isdist_fmap //=.
   rewrite isdist_fmap //=.
   apply/extensionP.
   rewrite isdist_fmap //=.
   rewrite isdist_fmap //=.
   exists S; exists S'; eexists; eexists; split.
   done.
   done.
   msimp; done.
   msimp; done.
   have -> : xt.2 = t.
    move: Hxt; simpl; msimp; simpl.
    move/support_bindP; elim => s'; elim => _; msimp; rewrite in_ret; move/eqP => -> //=.
  done.






  (* **** input *****  *)
  move => a mu eta [Hmu1 Hmu2] [Heta1 Heta2].
  move/extensionP.
  move/(_ Hmu2 Heta2).
  elim => S; elim => S'; elim => e; elim => t.
  elim => HS HS' heq1 heq2 HR; subst.
  move => Ha.
  move/seqDP: Ha; elim => htmp.
  rewrite !mem_cat.
  rewrite negb_or; move/andP; elim => Ha1 Ha2.
  move: htmp; rewrite !mem_cat; move/enum_orP; elim; move/andP; elim => Ha3 Ha4.
  rewrite act_i_comp_decomp_l; [idtac | done | done | done].
  have HiP': tag a \in inputs P'.
   move/andP: Hcomp; elim; move/seq_eqmemP => <-; done.
  rewrite act_i_comp_decomp_l; [idtac | done | done | done].
  move/h5: HR.
  move/(_ a).
  have Htmp: mvalid P (S ** (ret filter_tr P t)).
    split.
    move => x; move/support_bindP; elim => s; elim => _; msimp; rewrite in_ret; move/eqP => ->; apply filter_tr_valid.
    apply isdist_bind.
    done.
    intros; msimp; apply isdist_ret.
  move/(_ Htmp) {Htmp}.
  have Htmp: mvalid P' (S' ** (ret filter_tr P' t)).
    split.
    move => x; move/support_bindP; elim => s; elim => _; msimp; rewrite in_ret; move/eqP => ->; apply filter_tr_valid.
    apply isdist_bind.
    done.
    intros; msimp; apply isdist_ret.
  move/(_ Htmp) {Htmp}.
  move/(_ Ha3).
  elim => l; move/and3P; elim => Hl1 Hl2 Hl3.
  rewrite (act_i_filter_tr P) (act_i_filter_tr P') 2!mbindA.
  rewrite (eqP Hl1) (eqP Hl2); msimp; apply closure_bind => p Hp.
  move/and3P: (allP Hl3 _ Hp); elim => Hp1 Hp2 Hp3.
  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists (p.1 <$> fst); exists (p.2 <$> fst); eexists; eexists; split.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  msimp; done.
  msimp; done.
  msimp.
  rewrite !mem_cat Ha3 HiP' !orTb.
  have -> : (x <- p.1; ret (x.1, a :: filter_tr P t)) = p.1.
    rewrite -(bind_ret p.1) mbindA; apply mbind_eqP => x Hx; msimp.
    have <- : x.2 = a :: filter_tr P t.
    have: x \in support (p <- l; p.1).
    apply/support_bindP; exists p; split; done.
    rewrite -(eqP Hl1); rewrite /act_i; msimp.
    move/support_bindP; elim => s'; elim => _.
    move/support_bindP; elim => s''; elim => _.
    rewrite in_ret; move/eqP => -> //=.
    destruct x; done.
  have -> : (x <- p.2; ret (x.1, a :: filter_tr P' t)) = p.2.
    rewrite -(bind_ret p.2) mbindA; apply mbind_eqP => x Hx; msimp.
    have <- : x.2 = a :: filter_tr P' t.
    have: x \in support (p <- l; p.2).
    apply/support_bindP; exists p; split; done.
    rewrite -(eqP Hl2); rewrite /act_i; msimp.
    move/support_bindP; elim => s'; elim => _.
    move/support_bindP; elim => s''; elim => _.
    rewrite in_ret; move/eqP => -> //=.
    destruct x; done.
  done.

  have Ha5: tag a \notin inputs P'.
   move/andP: Hcomp; elim; move/seq_eqmemP => <-; done.
  have Ha6: tag a \notin outputs P'.
   move/andP: Hcomp; elim => _; move/seq_eqmemP => <-; done.
  rewrite act_i_comp_decomp_r; [idtac | done | done | done].
  rewrite act_i_comp_decomp_r; [idtac | done | done | done].
  rewrite (mbind_swap S) (mbind_swap S'); apply closure_bind => xt hxt.

  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists S; exists S'; eexists; eexists; split.
  done.
  done.
  msimp; done.
  msimp; done.
  simpl.
  rewrite !mem_cat (negbTE Ha1) (negbTE Ha4) (negbTE Ha5) (negbTE Ha6) //=.


  have Ha5 : tag a \in inputs P'.
   move/andP: Hcomp; elim; move/seq_eqmemP => <-; done.
  have Ha6: tag a \notin outputs P'.
   move/andP: Hcomp; elim => _; move/seq_eqmemP => <-; done.
   
  rewrite act_i_comp_decomp_lr; [idtac | done | done]. 
  rewrite act_i_comp_decomp_lr; [idtac | done | done]. 
  rewrite (mbind_swap (act_i P _ _)) (mbind_swap (act_i P' _ _)).
  apply closure_bind => xt Hxt.
  move/h5: HR.
  move/(_ a).
  have Htmp: mvalid P (S ** (ret filter_tr P t)).
    split.
    move => x; move/support_bindP; elim => s; elim => _; msimp; rewrite in_ret; move/eqP => ->; apply filter_tr_valid.
    apply isdist_bind.
    done.
    intros; msimp; apply isdist_ret.
  move/(_ Htmp) {Htmp}.
  have Htmp: mvalid P' (S' ** (ret filter_tr P' t)).
    split.
    move => x; move/support_bindP; elim => s; elim => _; msimp; rewrite in_ret; move/eqP => ->; apply filter_tr_valid.
    apply isdist_bind.
    done.
    intros; msimp; apply isdist_ret.
  move/(_ Htmp) {Htmp}.
  move/(_ Ha3).
  elim => l; move/and3P; elim => Hl1 Hl2 Hl3.
  rewrite (act_i_filter_tr P) (act_i_filter_tr P') 2!mbindA.
  rewrite (eqP Hl1) (eqP Hl2); msimp.
  apply closure_bind => p Hp.
  move/and3P: (allP Hl3 _ Hp); elim => Hp1 Hp2 Hp3.
  apply id_closure.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  apply/extensionP.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  exists (p.1 <$> fst); exists (p.2 <$> fst); eexists; eexists; split.
  rewrite isdist_fmap //=.
  rewrite isdist_fmap //=.
  msimp; done.
  msimp; done.
  msimp.
  rewrite !mem_cat Ha3 Ha5 !orTb //=.
  have -> : (x <- p.1; ret (x.1, a :: filter_tr P t)) = p.1.
      rewrite -(bind_ret p.1) mbindA; apply mbind_eqP => x Hx; msimp.
      have: x \in support (p <- l; p.1).
       apply/support_bindP; exists p; done.
      rewrite -(eqP Hl1) /act_i; msimp.
      move/support_bindP; elim => s; elim => _.
      move/support_bindP; elim => s'; elim => _.
      rewrite in_ret; move/eqP => -> //=.
  have -> : (x <- p.2; ret (x.1, a :: filter_tr P' t)) = p.2.
      rewrite -(bind_ret p.2) mbindA; apply mbind_eqP => x Hx; msimp.
      have: x \in support (p <- l; p.2).
       apply/support_bindP; exists p; done.
      rewrite -(eqP Hl2) /act_i; msimp.
      move/support_bindP; elim => s; elim => _.
      move/support_bindP; elim => s'; elim => _.
      rewrite in_ret; move/eqP => -> //=.
  done.
Qed.

Theorem ShSim_refines {G D : ctx} (P P' : PIOA G D) R (hc : comparable P P') :
  ShSim P P' R -> refines P P' hc.
  intros.
  move => D' E He.
  eapply InternalSim_sound; intros.
  instantiate (1 := fun x => (nil, x, nil)); simpl.
  simpl in H0.
  rewrite mem_cat; move: hc.
  rewrite /comparable; move/andP; elim => _; move/seq_eqmemP => <-.
  rewrite mem_cat //= in H0.

  eapply shSim_Internal.
  elim (andP He); done.
  eapply shSim_comp.
  done.
  done.
  apply H.
  elim (andP He); done.
Qed.

         



