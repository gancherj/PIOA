
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum Action.

Lemma neqnS (x : nat) :
  (x) != (succn x).
  by induction x.
Qed.

Definition ocons_ohead {A : eqType} (oat : seq A) (t : seq A) :=
  if ((size oat == succn (size t)) && ((List.tl oat) == t)) then ohead oat else None.

Lemma ocons_ohead_cons {A : eqType} (a : A) (t : seq A) :
  ocons_ohead (a :: t) t = Some a.
rewrite /ocons_ohead.
simpl.
rewrite !eq_refl //=.
Qed.

Lemma ocons_ohead_tt {A : eqType} (t : seq A) :
  ocons_ohead t t = None.
  rewrite /ocons_ohead (negbTE (neqnS _)) //=.
Qed.

Inductive ocons_ohead_spec {A : eqType} (t' t : seq A) : Prop :=
  | ocons_ohead_1 a : t' = a :: t -> ocons_ohead t' t = Some a -> ocons_ohead_spec t' t
  | ocons_ohead_2 : ocons_ohead t' t = None -> ocons_ohead_spec t' t.

Lemma ocons_oheadP {A : eqType} (t' t : seq A) : ocons_ohead_spec t' t.
  caseOn ((size t' == succn (size t)) && ((List.tl t') == t)).
  move => H.
  move:  (andP H); elim => /eqP h1 /eqP h2; subst.
  have: exists a, t' = a :: (List.tl t').
  induction t'.
  simpl in h1; done.
  exists a.
  simpl; done.
  elim => a Ht'; subst.
  apply (ocons_ohead_1 _ _ a).
  done.
  rewrite /ocons_ohead.
  rewrite H.
  rewrite Ht'; done.
  move => H; apply ocons_ohead_2.
  rewrite /ocons_ohead.
  rewrite (negbTE H); done.
Qed.

Definition compatible {Gamma Delta Delta' : ctx} (P1 : PIOA Gamma Delta) (P2 : PIOA Gamma Delta') :=
  seq_disjoint (outputs P1) (outputs P2).

(* TODO: unify monad syntax *)
Check omap.
Check obind.


Definition compPIOAtr {Gamma Delta Delta' : ctx} (P1 : PIOA Gamma Delta) (P2 : PIOA Gamma Delta') (s : St P1 * St P2) (h_a : action (Delta :+: Delta') + action Gamma) : option {meas (St P1) * (St P2)} :=
    match h_a with
    | inl (existT (inl ha) m) =>
      (tr P1 s.1 (inl (mkact Delta ha m))) <$>o (fun (mu : {meas St P1}) => (s' <- mu; ret (s', s.2)))
    | inl (existT (inr hb) m) =>
      (tr P2 s.2 (inl (mkact Delta' hb m))) <$>o (fun (mu : {meas St P2}) => (s' <- mu; ret (s.1, s')))
    | inr a => 
      match tag a \in (inputs P1 ++ outputs P1), tag a \in (inputs P2 ++ outputs P2) with
      | true, true =>
        (tr P1 s.1 (inr a)) >>=o fun (m1 : {meas St P1}) => (tr P2 s.2 (inr a)) >>=o fun (m2 : {meas St P2}) => Some (x <- m1; y <- m2; ret (x,y))

      | true, false => (tr P1 s.1 (inr a)) <$>o fun (mu : {meas St P1}) => (s' <- mu; ret (s', s.2))
      | false, true => (tr P2 s.2 (inr a)) <$>o fun (mu : {meas St P2}) => (s' <- mu; ret (s.1, s'))
      | false, false => None end
        end.

Lemma compPIOAtr_dist {G D D' : ctx} (P1 : PIOA G D) (P2 : PIOA G D') s h mu :
  compPIOAtr P1 P2 s h = Some mu -> isdist mu.
  rewrite /compPIOAtr.
  case h.
  case.
  case.
  move => a p.
  remember (tr P1 s.1 (inl (mkact D a p))) as o; destruct o; simpl.
  inj.
  rewrite isdist_fmap; eapply tr_isdist; symmetry; apply Heqo.
  done.

  move => b p.
  remember (tr P2 s.2 (inl (mkact D' b p))) as o; destruct o; simpl.
  inj.
  rewrite isdist_fmap ; eapply tr_isdist; symmetry; apply Heqo.
  done.

  move => a.
  caseOn (tag a \in inputs P1 ++ outputs P1).
  move => ->.
  caseOn (tag a \in inputs P2 ++ outputs P2).
  move => ->.
  move/eqP/obind_eq_some; elim => d; elim => Hd.
  move/eqP/obind_eq_some; elim => d'; elim => Hd'.
  inj.
  apply isdist_bind.
  eapply tr_isdist; apply Hd.
  intros; rewrite isdist_fmap; eapply tr_isdist; apply Hd'.
  move => heq; rewrite (negbTE heq).
  move/eqP/obind_eq_some; elim => d; elim => Hd.
  inj; apply isdist_bind.
  eapply tr_isdist; apply Hd.
  intros; apply isdist_ret.
  move => heq; rewrite (negbTE heq).
  move/eqP.
  caseOn (tag a \in inputs P2 ++ outputs P2).
  move => ->.
  move/obind_eq_some; elim => d; elim => Hd.
  inj; rewrite isdist_fmap; eapply tr_isdist; apply Hd.
  move => hneq; rewrite (negbTE hneq).
  done.
Qed.

Section CompPIOADef.
  Context {Gamma D D' : ctx} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D').

Lemma compPIOA1 :  seq_disjoint (seqD (inputs P1 ++ inputs P2) (outputs P1 ++ outputs P2))
    (outputs P1 ++ outputs P2).
  rewrite /seq_disjoint.
  apply/allP => x Hx.
  move/seqDP: Hx; elim => Hx1 Hx2.
  rewrite -notin_seq_all; done.
Qed.

Lemma compPIOA2 : forall (s : [finType of St P1 * St P2]) (h : cdom (D :+: D')) (m1 m2 : (D :+: D') h),
  compPIOAtr P1 P2 s (inl (mkact (D :+: D') h m1)) != None ->
  compPIOAtr P1 P2 s (inl (mkact (D :+: D') h m2)) != None -> m1 == m2.
  case => sa sb; case; rewrite //=.
  move => ha m1 m2.

  rewrite -omap_neq_none.
  rewrite -!omap_neq_none => h1 h2.
  by apply (ad_h (PIOAP P1) sa ha m1 m2).

  move => hb m1 m2; rewrite -!omap_neq_none => h1 h2.
  by apply (ad_h (PIOAP P2) sb hb m1 m2).
Qed.

Lemma compPIOA3 : 
  forall (s : [finType of St P1 * St P2]) (h : cdom Gamma) (m1 m2 : Gamma h), h \in (outputs P1 ++ outputs P2) ->
  compPIOAtr P1 P2 s (inr (mkact Gamma h m1)) != None ->
  compPIOAtr P1 P2 s (inr (mkact Gamma h m2)) != None -> m1 == m2.

  case => sa sb c m1 m2 Hc; rewrite /compPIOAtr.
  simpl.
  remember (c \in inputs P1 ++ outputs P1) as b1; symmetry in Heqb1; rewrite Heqb1.
  remember (c \in inputs P2 ++ outputs P2) as b2; symmetry in Heqb2; rewrite Heqb2.
  destruct b1; destruct b2.

  move/obind_neq_none; elim => x; elim => fx; elim => Heqtr1; rewrite //=.
  move/eqP/obind_eq_some; elim => x0; elim => htr2 h3.

  move/obind_neq_none; elim => y; elim => fy; elim => Heqtr2.
  move/eqP/obind_eq_some; elim => x0'; elim => htr2' h3'.

  rewrite mem_cat in Hc; move/orP: Hc; elim => Hc.

  apply (ad_v (PIOAP P1) sa); rewrite ?Heqtr1 ?Heqtr2 ?htr2 ?htr2' //=.
  apply (ad_v (PIOAP P2) sb); rewrite ?Heqtr1 ?Heqtr2 ?htr2 ?htr2' //=.

  have Hc2: c \notin outputs P2.
  apply contraT; rewrite negbK => Hc2.
  rewrite mem_cat Hc2 orbT //= in Heqb2.

  move/obind_neq_none; elim => x; elim => fx; elim => h1 h2.
  move/obind_neq_none; elim => x'; elim => fx'; elim => h1' h2'.
  apply (ad_v (PIOAP P1) sa); rewrite ?h1 ?h1' //=.
  rewrite mem_cat (negbTE Hc2) orbF //= in Hc.

  have Hc1: c \notin outputs P1.
  apply contraT; rewrite negbK => Hc1.
  rewrite mem_cat Hc1 orbT //= in Heqb1.

  move/obind_neq_none; elim => x; elim => fx; elim => h1 h2.
  move/obind_neq_none; elim => x'; elim => fx'; elim => h1' h2'.
  apply (ad_v (PIOAP P2) sb); rewrite ?h1 ?h1' //=.
  rewrite mem_cat (negbTE Hc1) orFb //= in Hc.
  done.
Qed.

Lemma compPIOA4 : 
  forall (s : [finType of St P1 * St P2]) (i : cdom Gamma),
  i \in seqD (inputs P1 ++ inputs P2) (outputs P1 ++ outputs P2) ->
  forall m : Gamma i, compPIOAtr P1 P2 s (inr (mkact Gamma i m)) != None.
  case => sa sb i; move/seqDP; elim.
  move/catP; elim; move/andP; elim => h1 h2 h3 m.

  rewrite /compPIOAtr //=.
  rewrite mem_cat h1 orTb //=.
  rewrite mem_cat negb_or in h3; move/andP: h3 => [h31 h32].
  rewrite mem_cat (negbTE h2) (negbTE h32) //=.
  have /opt_neq_none: tr P1 sa (inr (mkact Gamma i m)) != None by apply (i_a (PIOAP P1)).
  by elim => x ->.

  rewrite /compPIOAtr //=.
  rewrite mem_cat negb_or in h3; move/andP: h3 => [h31 h32].
  rewrite (mem_cat) (negbTE h2) (negbTE h31) //=.
  rewrite mem_cat h1 orTb //=.
  have /opt_neq_none: tr P2 sb (inr (mkact Gamma i m)) != None by apply (i_a (PIOAP P2)).
  by elim => x ->.

  rewrite /compPIOAtr //= mem_cat h1 orTb mem_cat h2 //=.
  have /opt_neq_none: tr P1 sa (inr (mkact Gamma i m)) != None by apply (i_a (PIOAP P1)).
  elim => x -> //=.
  have /opt_neq_none: tr P2 sb (inr (mkact Gamma i m)) != None by apply (i_a (PIOAP P2)).
  elim => y -> //=.
Qed.

Definition compPIOA_data : PIOA_data Gamma (D :+: D').
econstructor.
apply (start P1, start P2).
apply (seqD (inputs P1 ++ inputs P2) (outputs P1 ++ outputs P2)).
apply (outputs P1 ++ outputs P2).
apply (compPIOAtr P1 P2).
Defined.


Lemma compPIOA_spec : PIOA_spec compPIOA_data.
constructor.
apply compPIOA1.
apply compPIOA2.
apply compPIOA3.
apply compPIOA4.
apply compPIOAtr_dist.
Qed.

Definition compPIOA : PIOA Gamma (D :+: D').
  apply (mkPIOA _ _ compPIOA_data compPIOA_spec).
Defined.

End CompPIOADef.
Notation "P1 ||| P2" := (compPIOA P1 P2) (at level 70).



Section CompProps.

  Context {Gamma D D' : ctx} (P1 : PIOA Gamma D) (E : PIOA Gamma D') 
   (mu : {meas (St (P1 ||| E) * trace (P1 ||| E))}).

Lemma app_h_comp_l h s : app_h (P1 ||| E) (inl h) s = (x <- app_h P1 h s.1; ret (x, s.2)).
  rewrite /app_h //=.
  rewrite /pick_h //=.
  have:  (fun m => enabled (P1 ||| E) s (inl (mkact (D :+: D') (inl h) m))) =1
                  (fun m => enabled P1 s.1 (inl (mkact (D) h m))).
  simpl => m.
  rewrite /enabled //=.
  rewrite -omap_neq_none //=.
  move/eq_pick ->.
  case: pickP.
  rewrite //= => x Hx.

  remember (tr P1 s.1 (inl (mkact (D) h x))) as o; destruct o; rewrite //=.
  rewrite ret_bind; by destruct s.

  simpl; rewrite ret_bind; by destruct s.
Qed.

Lemma app_h_comp_r h s : app_h (P1 ||| E) (inr h) s = (x <- app_h E h s.2; ret (s.1, x)).
  rewrite /app_h //=.
  rewrite /pick_h //=.
  have:  (fun m => enabled (P1 ||| E) s (inl (mkact (D :+: D') (inr h) m))) =1
                  (fun m => enabled E s.2 (inl (mkact (D') h m))).
  simpl => m.
  rewrite /enabled //=.
  rewrite -omap_neq_none //=.
  move/eq_pick ->.
  case: pickP.
  rewrite //= => x Hx.
  remember (tr E s.2 (inl (mkact (D') h x))) as o; destruct o; rewrite //=.
  rewrite ret_bind; by destruct s.
  move => H; rewrite //= ret_bind. by destruct s.
Qed.

Lemma pick_v_comp_l c s (Hcompat : compatible P1 E) : c \in outputs P1 ->
  pick_v (P1 ||| E) c s = pick_v P1 c s.1.
  move => hc; rewrite /pick_v.
  have:  [pick m | enabled (P1 ||| E) s (inr (mkact Gamma c m)) ]  =
         [pick m | enabled P1 s.1 (inr (mkact Gamma c m)) ].
  apply eq_pick => x ; rewrite /enabled; simpl.
  move/seq_disjointP: Hcompat; move/(_ _ hc) => co2.
  rewrite !mem_cat hc (negbTE co2) orbT.
  remember (c \in inputs E); destruct b; rewrite //=.
  remember (tr P1 s.1 (inr (mkact Gamma c x))) as tr; destruct tr; simpl.
  rewrite -Heqtr //=.
  have /opt_neq_none: tr E s.2 (inr (mkact Gamma c x)) != None by apply (i_a (PIOAP E)).
  elim => z ->; done.

  rewrite -Heqtr //=.

  rewrite -omap_neq_none //=.
  move => ->.
  done.
Qed.

Lemma pick_v_comp_r c s (Hcompat : compatible P1 E) : c \in outputs E ->
  pick_v (P1 ||| E) c s = pick_v E c s.2.
  move => hc; rewrite /pick_v.
  have:  [pick m | enabled (P1 ||| E) s (inr (mkact Gamma c m)) ]  =
         [pick m | enabled E s.2 (inr (mkact Gamma c m)) ].
  apply eq_pick => x ; rewrite /enabled; simpl.
  rewrite /compatible seq_disjoint_sym in Hcompat.
  move/seq_disjointP: Hcompat; move/(_ _ hc) => co2.
  rewrite !mem_cat hc (negbTE co2) orbT.
  remember (c \in inputs P1); destruct b; rewrite //=.
  have /opt_neq_none: tr P1 s.1 (inr (mkact Gamma c x)) != None by apply (i_a (PIOAP P1)).
  elim => z ->; rewrite //=.

  remember (tr E s.2 (inr (mkact Gamma c x))) as tr; destruct tr; simpl.
  rewrite -Heqtr //=.
  rewrite -Heqtr //=.


  rewrite -omap_neq_none //=.
  move => ->.
  done.
Qed.

                                 


  Lemma app_v_comp_l_ext c s : compatible P1 E -> c \in outputs P1 -> c \notin inputs E ->
        app_v (P1 ||| E) c s =
        (p <- app_v P1 c s.1; 
           ret ((p.1, s.2), p.2)).
    move => hcompat h1 h2; simpl; rewrite /app_v.
    rewrite pick_v_comp_l; rewrite //=.
  remember (pick_v P1 c s.1) as oa; destruct oa. 
  symmetry in Heqoa; apply pick_vP in Heqoa; last by done.
  move/andP: Heqoa => [h3 h4].
  rewrite !mem_cat (eqP h4) h1 (negbTE h2) orbT //=.
  rewrite (negbTE (seq_disjointP _  _ hcompat _ h1)).
  remember (tr P1 s.1 (inr s0)) as o; destruct o; rewrite -Heqo //=.
  rewrite !mbindA; apply mbind_eqP => x Hx; rewrite !ret_bind //=.
  rewrite ret_bind //=; by destruct s.
  rewrite ret_bind //=; by destruct s.
  Qed.

  Lemma app_v_comp_r_ext c s : compatible P1 E -> c \in outputs E -> c \notin inputs P1 ->
        app_v (P1 ||| E) c s =
        (p <- app_v E c s.2; 
           ret ((s.1, p.1), p.2)).
    move => hcompat h1 h2; simpl; rewrite /app_v.
    rewrite pick_v_comp_r; rewrite //=.
  remember (pick_v E c s.2) as oa; destruct oa. 
  symmetry in Heqoa; apply pick_vP in Heqoa; last by done.
  move/andP: Heqoa => [h3 h4].
  rewrite !mem_cat (eqP h4) h1 (negbTE h2) orbT //=.
  rewrite /compatible seq_disjoint_sym in hcompat.
  rewrite (negbTE (seq_disjointP _  _ hcompat _ h1)).
  remember (tr E s.2 (inr s0)) as o; destruct o; rewrite -Heqo //=.
  rewrite !mbindA; apply mbind_eqP => x Hx; rewrite !ret_bind //=.
  rewrite ret_bind //=; by destruct s.
  rewrite ret_bind //=; by destruct s.
  Qed.

  Lemma app_v_comp_l_int c s : compatible P1 E -> c \in outputs P1 -> c \in inputs E ->
        app_v (P1 ||| E) c s =
        (p <- app_v P1 c s.1;
        match p with
             | (s1, Some a) =>
               s2 <- app_i E a s.2;
                 ret ((s1, s2), Some a)
             | _ => ret (s, None)
                        end).
    intros.
    rewrite /app_v.
    rewrite pick_v_comp_l; rewrite //=.
    remember (pick_v P1 c s.1) as oa; destruct oa. 
    symmetry in Heqoa; apply pick_vP in Heqoa.
    elim (andP Heqoa) => h1 h2.
    rewrite (eqP h2) !mem_cat H0 H1 orbT orTb.
    remember (tr P1 s.1 (inr s0)) as t; destruct t; rewrite -Heqt; simpl.
    rewrite !mbindA.
    rewrite /app_i.
    symmetry; etransitivity.
    apply mbind_eqP => y Hy.
    rewrite ret_bind //=.
    remember (tr E s.2 (inr s0)) as t2; destruct t2; rewrite -Heqt2; simpl.
    rewrite !mbindA; apply mbind_eqP => x Hx; rewrite !mbindA; apply mbind_eqP => y Hy; rewrite ret_bind //=.

    have: tr E s.2 (inr s0) != None.
    apply inputEnabled.
    rewrite (eqP h2); done.
    rewrite -Heqt2 //=.
    rewrite ret_bind //=.
    done.
    rewrite ret_bind //=.
  Qed.

  Lemma app_v_comp_r_int c s : compatible P1 E -> c \in outputs E -> c \in inputs P1 ->
        app_v (P1 ||| E) c s =
        (p <- app_v E c s.2;
        match p with
             | (s2, Some a) =>
               s1 <- app_i P1 a s.1;
                 ret ((s1, s2), Some a)
             | _ => ret (s, None)
                        end).
    intros.
    rewrite /app_v.
    rewrite pick_v_comp_r; rewrite //=.
    remember (pick_v E c s.2) as oa; destruct oa. 
    symmetry in Heqoa; apply pick_vP in Heqoa.
    elim (andP Heqoa) => h1 h2.
    rewrite (eqP h2) !mem_cat H0 H1 orbT orTb.

    rewrite /app_i.
    remember (tr E s.2 (inr s0)) as t; destruct t; rewrite -Heqt; simpl.
    rewrite !mbindA.
    rewrite /app_i.
    symmetry; etransitivity.
    apply mbind_eqP => y Hy.
    rewrite ret_bind //=.
    remember (tr P1 s.1 (inr s0)) as t2; destruct t2; rewrite -Heqt2; simpl.

    rewrite !mbindA mbind_swap ; apply mbind_eqP => x Hx; rewrite !mbindA; apply mbind_eqP => y Hy; rewrite ret_bind //=.

    have: tr P1 s.1 (inr s0) != None.
    apply inputEnabled.
    rewrite (eqP h2); done.
    rewrite -Heqt2 //=.
    rewrite /app_i ret_bind.

    remember (tr P1 s.1 (inr s0)) as t0; rewrite -Heqt0; destruct t0; done.
    done.

    rewrite ret_bind //=.
  Qed.

  Check app_i.
                                                                            
  Lemma app_i_comp_l a s : tag a \in inputs P1 -> tag a \notin inputs E -> tag a \notin outputs E -> 
                                 app_i (P1 ||| E) a s =
                                 (s' <- app_i P1 a s.1; ret (s', s.2)).
    intros; rewrite /app_i.
    simpl.
    rewrite !mem_cat.
    rewrite H (negbTE H0) (negbTE H1) //=.
    remember (tr P1 s.1 (inr a)); rewrite -Heqo; destruct o; simpl.
    done.
    rewrite !measE //=.
    destruct s; done.
  Qed.

  Lemma app_i_comp_r a s : tag a \notin inputs P1 -> tag a \in inputs E -> tag a \notin outputs P1 -> 
                                 app_i (P1 ||| E) a s =
                                 (s' <- app_i E a s.2; ret (s.1, s')).
    intros; rewrite /app_i.
    simpl.
    rewrite !mem_cat.
    rewrite (negbTE H) H0 (negbTE H1) //=.
    remember (tr E s.2 (inr a)); rewrite -Heqo; destruct o; simpl.
    done.
    rewrite !measE //=.
    destruct s; done.
  Qed.

  Lemma app_i_comp_lr a s : tag a \in inputs P1 -> tag a \in inputs E -> 
                                 app_i (P1 ||| E) a s =
                                 (app_i P1 a s.1) ** (app_i E a s.2).
    intros; rewrite /app_i.
    simpl.
    rewrite !mem_cat.
    rewrite H H0 //=.
    remember (tr P1 s.1 (inr a)) as o; rewrite -Heqo; destruct o; simpl.
    remember (tr E s.2 (inr a)) as o'; rewrite -Heqo'; destruct o'; simpl.
    done.
    Check inputEnabled.
    move: (inputEnabled E s.2 a H0).
    rewrite -Heqo' //=.
    move: (inputEnabled P1 s.1 a H).
    rewrite -Heqo //=.
  Qed.

  Check act.

  Lemma act_h_decomp_l h S e t :
    act (P1 ||| E) (inl (inl h)) ((S ** ret e) ** ret t) =
    act P1 (inl h) (S ** ret t) <$> (fun p => (p.1, e, p.2)).
    rewrite /act. 
    rewrite 4! mbindA.
    apply mbind_eqP => s Hs.
    msimp.
    rewrite app_h_comp_l; msimp.
    done.
  Qed.
  
  Lemma act_h_decomp_r h S e t :
    act (P1 ||| E) (inl (inr h)) ((S ** ret e) ** ret t) =
    (s <- S; p <- act E (inl h) ((ret e) ** ret t); ret (s, p.1, p.2)). 
    rewrite /act. 
    rewrite 3! mbindA; apply mbind_eqP => s Hs; msimp.
    rewrite app_h_comp_r; msimp.
    done.
  Qed.

  Lemma act_v_comp_decomp_l_ext a S e t : compatible P1 E -> a \in outputs P1 -> a \notin inputs E ->
                                act (P1 ||| E) (inr a) ((S ** ret e) ** ret t) =
                                (p <- act P1 (inr a) (S ** ret t); ret (p.1, e, p.2)).
    move => H h1 h2; rewrite /act 4!mbindA; apply mbind_eqP => s Hs; msimp.
    rewrite app_v_comp_l_ext; msimp; done.
  Qed.

  Lemma act_v_comp_decomp_r_ext a S e t : compatible P1 E -> a \in outputs E -> a \notin inputs P1 ->
                                act (P1 ||| E) (inr a) ((S ** ret e) ** ret t) =
                                (s <- S; p <- act E (inr a) ((ret e) ** ret t); ret (s, p.1, p.2)).
    move => H h1 h2; rewrite /act 3!mbindA; apply mbind_eqP => s Hs; msimp.
    rewrite app_v_comp_r_ext; msimp; done.
  Qed.

  Lemma act_v_comp_decomp_l_int a S e t : compatible P1 E -> a \in outputs P1 -> a \in inputs E ->
                                act (P1 ||| E) (inr a) ((S ** ret e) ** ret t) =
                                (p <- act P1 (inr a) (S ** ret t); match ocons_ohead p.2 t with
                                                                     | Some a => e' <- app_i E a e; ret (p.1, e', p.2)
                                                                     | None => ret (p.1, e, p.2)
                                                                                            end).
    move => H h1 h2; rewrite /act.
    rewrite 4!mbindA; apply mbind_eqP => s Hs; msimp.
    rewrite app_v_comp_l_int; msimp.
    case: (app_vP P1 a s h1).
    move => m eta Htr ->; msimp; rewrite ocons_ohead_cons; done.
    move => H1 ->; msimp; rewrite ocons_ohead_tt; done.
    done.
    done.
    done.
  Qed.

  Lemma act_v_comp_decomp_r_int a S e t : compatible P1 E -> a \in inputs P1 -> a \in outputs E ->
                                act (P1 ||| E) (inr a) ((S ** ret e) ** ret t) =
                                (s <- S; p <- act E (inr a) ((ret e) ** ret t);
                                   match ocons_ohead p.2 t with
                                   | Some a => s' <- app_i P1 a s; ret (s', p.1, p.2)
                                   | None => ret (s, p.1, p.2) end).
    move => H h1 h2; rewrite /act.
    rewrite 3!mbindA; apply mbind_eqP => s Hs; msimp.
    rewrite app_v_comp_r_int; msimp.
    case: (app_vP E a e h2).
    move => m eta Htr ->; msimp; rewrite ocons_ohead_cons; done.
    move => H1 ->; msimp; rewrite ocons_ohead_tt; done.
    done.
    done.
    done.
  Qed.

Definition act_i {G D : ctx} (P : PIOA G D) (a : action G) (mu : {meas St P * trace P}) :=
  (xt <- mu; s' <- app_i P a xt.1; ret (s', a :: xt.2)).

  Lemma act_i_comp_decomp_l a S e t :
    tag a \in inputs P1 -> tag a \notin inputs E -> tag a \notin outputs E -> 
            act_i (P1 ||| E) a ((S ** ret e) ** ret t) =
            (st <- act_i P1 a (S ** ret t); ret (st.1, e, a :: t)).
    move => ha1 ha2 ha3; rewrite /act_i 4!mbindA.
    apply mbind_eqP => s Hs; msimp.
    rewrite app_i_comp_l.
    msimp; done.
    done.
    done.
    done.
  Qed.

  Lemma act_i_comp_decomp_r a S e t :
    tag a \in inputs E -> tag a \notin inputs P1 -> tag a \notin outputs P1 -> 
            act_i (P1 ||| E) a ((S ** ret e) ** ret t) =
            (s <- S; et <- act_i E a ((ret e) ** ret t); ret (s, et.1, a :: t)).
    move => ha1 ha2 ha3; rewrite /act_i 3!mbindA.
    apply mbind_eqP => s Hs; msimp.
    rewrite app_i_comp_r.
    msimp; done.
    done.
    done.
    done.
  Qed.

  Lemma act_i_comp_decomp_lr a S e t :
    tag a \in inputs E -> tag a \in inputs P1 -> 
            act_i (P1 ||| E) a ((S ** ret e) ** ret t) =
            (st <- act_i P1 a (S ** ret t); e' <- app_i E a e; ret (st.1, e', a :: t)).
    move => ha1 ha2 ; rewrite /act_i 4!mbindA.
    apply mbind_eqP => s Hs; msimp.
    rewrite app_i_comp_lr.
    msimp; done.
    done.
    done.
  Qed.

End CompProps.


Lemma compatible_symm {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') :
  compatible P P' = compatible P' P.
  rewrite /compatible seq_disjoint_sym //=. 
Qed.