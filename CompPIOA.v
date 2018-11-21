
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum Action.

Definition compatible {Gamma Delta Delta' : ctx} (P1 : PIOA Gamma Delta) (P2 : PIOA Gamma Delta') :=
  seq_disjoint (outputs P1) (outputs P2).

(* TODO: unify monad syntax *)
Check omap.
Check obind.


Definition compPIOAtr {Gamma Delta Delta' : ctx} (P1 : PIOA Gamma Delta) (P2 : PIOA Gamma Delta') (s : St P1 * St P2) (h_a : action (Delta :+: Delta') + action Gamma) : option {meas (St P1) * (St P2)} :=
    match h_a with
    | inl (existT (inl ha) m) =>
      (tr P1 s.1 (inl (mkact Delta ha m))) <$>o fun mu => (s' <- mu; ret (s', s.2))
    | inl (existT (inr hb) m) =>
      (tr P2 s.2 (inl (mkact Delta' hb m))) <$>o fun mu => (s' <- mu; ret (s.1, s'))
    | inr a => 
      match tag a \in (inputs P1 ++ outputs P1), tag a \in (inputs P2 ++ outputs P2) with
      | true, true =>
        (tr P1 s.1 (inr a)) >>=o fun m1 => (tr P2 s.2 (inr a)) >>=o fun m2 => Some (x <- m1; y <- m2; ret (x,y))

      | true, false => (tr P1 s.1 (inr a)) <$>o fun mu => (s' <- mu; ret (s', s.2))
      | false, true => (tr P2 s.2 (inr a)) <$>o fun mu => (s' <- mu; ret (s.1, s'))
      | false, false => None end
        end.

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
  move => ha m1 m2; rewrite -!omap_neq_none => h1 h2.
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
Qed.

Definition compPIOA : PIOA Gamma (D :+: D').
  apply (mkPIOA _ _ compPIOA_data compPIOA_spec).
Defined.

End CompPIOADef.
Notation "P1 ||| P2" := (compPIOA P1 P2) (at level 70).

(*

Section CompProps.

  Context {Gamma D D' : ctx} (P1 : PIOA Gamma D) (E : PIOA Gamma D') 
   (mu : {meas (St (P1 ||| E) * trace (P1 ||| E))}).

Lemma app_h_comp_l h s : app_h (P1 ||| E) (inl h) s = (x <- app_h P1 h s.1; ret (x, s.2)).
  rewrite /app_h //=.
  rewrite /achoose_h //=.
  have:  (fun m => enabled (P1 ||| E) s (inl (mkact (D :+: D') (inl h) m))) =1
                  (fun m => enabled P1 s.1 (inl (mkact (D) h m))).
  simpl => m.
  rewrite /enabled //=.
  rewrite -omap_neq_none //=.
  move/eq_pick ->.
  case: pickP.
  rewrite //= => x Hx.
  remember (tr P1 s.1 (inl (mkact (D) h x))) as o; rewrite -Heqo; destruct o; rewrite //=.
  rewrite ret_bind; by destruct s.
  move => H; rewrite //= ret_bind. by destruct s.
Qed.

Lemma app_h_comp_r h s : app_h (P1 ||| E) (inr h) s = (x <- app_h E h s.2; ret (s.1, x)).
  rewrite /app_h //=.
  rewrite /achoose_h //=.
  have:  (fun m => enabled (P1 ||| E) s (inl (mkact (D :+: D') (inr h) m))) =1
                  (fun m => enabled E s.2 (inl (mkact (D') h m))).
  simpl => m.
  rewrite /enabled //=.
  rewrite -omap_neq_none //=.
  move/eq_pick ->.
  case: pickP.
  rewrite //= => x Hx.
  remember (tr E s.2 (inl (mkact (D') h x))) as o; rewrite -Heqo; destruct o; rewrite //=.
  rewrite ret_bind; by destruct s.
  move => H; rewrite //= ret_bind. by destruct s.
Qed.

Lemma achoose_v_comp_l c s (Hcompat : compatible P1 E) : c \in outputs P1 ->
  achoose_v (P1 ||| E) c s = achoose_v P1 c s.1.
  move => hc; rewrite /achoose_v.
  have:  [pick m | enabled (P1 ||| E) s (inr (mkact Gamma c m)) ]  =
         [pick m | enabled P1 s.1 (inr (mkact Gamma c m)) ].
  apply eq_pick => x ; rewrite /enabled; simpl.
  move/seq_disjointP: Hcompat; move/(_ _ hc) => co2.
  rewrite !mem_cat hc (negbTE co2) orbT.
  remember (c \in inputs E); destruct b; rewrite //=.
  remember (tr P1 s.1 (inr (mkact Gamma c x))) as tr; destruct tr; simpl.
  rewrite -Heqtr //=.
  have /opt_neq_none: tr E s.2 (inr (mkact Gamma c x)) != None by apply (i_a E).
  elim => z ->; done.

  rewrite -Heqtr //=.

  rewrite -omap_neq_none //=.
  move => ->.
  done.
Qed.

Lemma achoose_v_comp_r c s (Hcompat : compatible P1 E) : c \in outputs E ->
  achoose_v (P1 ||| E) c s = achoose_v E c s.2.
  move => hc; rewrite /achoose_v.
  have:  [pick m | enabled (P1 ||| E) s (inr (mkact Gamma c m)) ]  =
         [pick m | enabled E s.2 (inr (mkact Gamma c m)) ].
  apply eq_pick => x ; rewrite /enabled; simpl.
  rewrite /compatible seq_disjoint_sym in Hcompat.
  move/seq_disjointP: Hcompat; move/(_ _ hc) => co2.
  rewrite !mem_cat hc (negbTE co2) orbT.
  remember (c \in inputs P1); destruct b; rewrite //=.
  have /opt_neq_none: tr P1 s.1 (inr (mkact Gamma c x)) != None by apply (i_a P1).
  elim => z ->; rewrite //=.

  remember (tr E s.2 (inr (mkact Gamma c x))) as tr; destruct tr; simpl.
  rewrite -Heqtr //=.
  rewrite -Heqtr //=.


  rewrite -omap_neq_none //=.
  move => ->.
  done.
Qed.

  Lemma hidden1P hl :
        act (P1 ||| E) (inl (inl hl)) mu =
        (st <- mu; s' <- app_h P1 hl st.1.1; ret ((s', st.1.2), st.2)).
  simpl.
  apply mbind_eqP => xt Hxt.
  rewrite app_h_comp_l mbindA; apply mbind_eqP => s' Hs'; rewrite ret_bind //=.
  Qed.

  Lemma hidden2P hr :
        act (P1 ||| E) (inl (inr hr)) mu =
        (st <- mu; s' <- app_h E hr st.1.2; ret ((st.1.1, s'), st.2)).
  simpl; apply mbind_eqP => xt Hxt.
  rewrite app_h_comp_r mbindA; apply mbind_eqP => s' Hs'; rewrite ret_bind //=.
  Qed.

  Lemma out1_extP ol (Hcompat : compatible P1 E) : ol \in outputs P1 -> ol \notin inputs E ->
        act (P1 ||| E) (inr ol) mu =
        (st <- mu; let ox := achoose_v P1 ol st.1.1 in s' <- app_ova P1 ox st.1.1; ret ((s', st.1.2), ocons ox st.2)).
  move => H1 H2; simpl; apply mbind_eqP => st Hst.
  rewrite achoose_v_comp_l; rewrite //=.

  remember (achoose_v P1 ol st.1.1) as oa; destruct oa; rewrite -Heqoa.
  simpl.
  symmetry in Heqoa; apply achoose_vP in Heqoa; last by done.
  move/andP: Heqoa => [h1 h2].
  rewrite (eqP h2).
  rewrite !mem_cat H1 (negbTE H2) orbT //=.
  move/seq_disjointP: Hcompat;move/(_ _ H1) => Hn; rewrite (negbTE Hn)//=.

  remember (tr P1 st.1.1 (inr s)) as t; destruct t; rewrite -Heqt ; simpl.
  rewrite mbindA; apply mbind_eqP => s' Hs'.
  rewrite ret_bind; done.

  rewrite !ret_bind; destruct st as [[? ?] ?]; done. 

  simpl; rewrite !ret_bind; destruct st as [[? ?] ?]; done.
  Qed.


  Lemma out2_extP ol (Hcompat : compatible P1 E) : ol \in outputs E -> ol \notin inputs P1 ->
        act (P1 ||| E) (inr ol) mu =
        (st <- mu; let ox := achoose_v E ol st.1.2 in s' <- app_ova E ox st.1.2; ret ((st.1.1, s'), ocons ox st.2)).
  move => H1 H2; simpl; apply mbind_eqP => st Hst.
  rewrite achoose_v_comp_r; rewrite //=.

  remember (achoose_v E ol st.1.2) as oa; destruct oa; rewrite -Heqoa.
  simpl.
  symmetry in Heqoa; apply achoose_vP in Heqoa; last by done.
  move/andP: Heqoa => [h1 h2].
  rewrite (eqP h2).
 rewrite !mem_cat H1 (negbTE H2) orbT; simpl.
 
  rewrite /compatible seq_disjoint_sym in Hcompat; move/seq_disjointP: Hcompat; move/(_ _ H1) => Hn; rewrite (negbTE Hn)//=.

  remember (tr E st.1.2 (inr s)) as t; destruct t; rewrite -Heqt ; simpl.
  rewrite mbindA; apply mbind_eqP => s' Hs'.
  rewrite ret_bind; done.

  rewrite !ret_bind; destruct st as [[? ?] ?]; done. 

  simpl; rewrite !ret_bind; destruct st as [[? ?] ?]; done.
  Qed.

  Lemma out1_intP ol (Hc : compatible P1 E) : ol \in outputs P1 -> ol \in inputs E ->
        act (P1 ||| E) (inr ol) mu =
        (st <- mu; let ox := achoose_v P1 ol st.1.1 in s1' <- app_ova P1 ox st.1.1; s2' <- app_ova E ox st.1.2; ret ((s1', s2'), ocons ox st.2)). 
  move => h1 h2; simpl; apply mbind_eqP => st Hst; simpl; rewrite achoose_v_comp_l.
  remember (achoose_v P1 ol st.1.1) as oa; destruct oa; rewrite -Heqoa; simpl.
  symmetry in Heqoa; apply achoose_vP in Heqoa; last by done.
  move/andP: Heqoa => [h3 h4].
  rewrite (eqP h4) !mem_cat h1 h2 orbT //=.
  remember (tr P1 st.1.1 (inr s)) as ot; destruct ot; rewrite -Heqot; simpl.
  have: tr E st.1.2 (inr s) != None.
   by apply (inputEnabled E); rewrite (eqP h4).
  move/opt_neq_none; elim => tE HeqtE.
  rewrite HeqtE; simpl.
  rewrite !mbindA; apply mbind_eqP => s' Hs'.
  rewrite mbindA; apply mbind_eqP => y Hy.
  rewrite ret_bind; done.
  rewrite /enabled -Heqot //= in h3.

  rewrite !ret_bind; destruct st as [[? ?] ?]; done.
  done.
  done.
 Qed.

  Lemma out2_intP ol (Hc : compatible P1 E) : ol \in outputs E -> ol \in inputs P1 ->
        act (P1 ||| E) (inr ol) mu =
        (st <- mu; let ox := achoose_v E ol st.1.2 in s1' <- app_ova P1 ox st.1.1; s2' <- app_ova E ox st.1.2; ret ((s1', s2'), ocons ox st.2)). 
  move => h1 h2; simpl; apply mbind_eqP => st Hst; simpl; rewrite achoose_v_comp_r.
  remember (achoose_v E ol st.1.2) as oa; destruct oa; rewrite -Heqoa; simpl.
  symmetry in Heqoa; apply achoose_vP in Heqoa; last by done.
  move/andP: Heqoa => [h3 h4].
  rewrite (eqP h4) !mem_cat h1 h2 orbT //=.
  have: tr P1 st.1.1 (inr s) != None.
    by apply (inputEnabled P1); rewrite (eqP h4).
  move/opt_neq_none; elim => t1 Heqt1.
  rewrite Heqt1; simpl.

  remember (tr E st.1.2 (inr s)) as ot; destruct ot; rewrite -Heqot; simpl.
  rewrite mbindA; apply mbind_eqP => s' Hs'; rewrite mbindA; apply mbind_eqP => x Hx.
  rewrite ret_bind //=.
  rewrite /enabled -Heqot //= in h3.

  rewrite !ret_bind; destruct st as [[? ?] ?]; done.
  done.
  done.
 Qed.  
  
End CompProps.
*)