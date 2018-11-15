
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum CompPIOA Lifting.

Check channel.
Print channel.
Definition is_chan {Gamma D : context} (P : PIOA Gamma D) (hc : (H P) + (C P)) :=
  match hc with
  | inl _ => true
  | inr c =>
    c \in (inputs P ++ outputs P)
            end.
  
Definition comparable {Gamma D D' : context} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') := (inputs P1 ==i inputs P2) && (outputs P1 ==i outputs P2).

Definition protocol_for {Gamma D : context} (P : PIOA Gamma D) (x : seq (cdom D + cdom Gamma)) := all (is_chan P) x.

Definition env {Gamma D D' : context} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') :=
  compatible P1 P2 && closed (P1 ||| P2).
  
Definition refines  {Gamma D D' : context} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') (hc : comparable P1 P2) :=
  forall {D'' : context} (E: PIOA Gamma D''), env P1 E -> forall g1, protocol_for (P1 ||| E) g1 -> exists g2, protocol_for (P2 ||| E) g2 /\ 
        measMap (run (P1 ||| E) (g1)) snd = measMap (run (P2 ||| E) (g2)) snd.


Record simulation_sameh  {Gamma D : context} (P1 P2 : PIOA Gamma D) (Hcomp : comparable P1 P2)
       (R : {meas (St P1) * (trace P1)} -> {meas (St P2) * (trace P2)} -> bool) :=
  {
    sim_trace_eq : forall mu eta, R mu eta -> forall p1 p2, p1 \in support mu -> p2 \in support eta -> p1.2 = p2.2;
    sim_start : R (initDist P1) (initDist P2);
    sim_step_lc : forall mu eta (hc : (H P1) + (C P1)), locally_controlled P1 hc -> R mu eta -> lifting R (act P1 hc mu) (act P2 hc eta);
    sim_step_i : forall mu eta (a : action Gamma), (tag a \in inputs P1) -> R mu eta ->
                                                   lifting R (apply_i P1 a mu) (apply_i P2 a eta)
                          }. 

Definition proj_state_l {Gamma D D': context} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') (x : St (P1 ||| P2)) := x.1.
Definition proj_trace_l {Gamma D D' : context} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') (x : trace (P1 ||| P2)) :=
  filter (fun a => tag a \in (inputs P1 ++ outputs P1)) x.
Definition proj_mt_l {Gamma D D' : context} (P1 : PIOA Gamma D) (E : PIOA Gamma D') (mu : {meas (St (P1 ||| E)) * (trace (P1 ||| E))}) :=
  measMap mu (fun p => (proj_state_l P1 E p.1, proj_trace_l P1 E p.2)).

Definition extension {Gamma D D' D'' : context} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') (E : PIOA Gamma D'') (HE : env P1 E)
           (R : {meas (St P1 * trace P1)} -> {meas (St P2 * trace P2)} -> bool)
           (mu : {meas St (P1 ||| E) * trace (P1 ||| E)})
           (eta : {meas St (P2 ||| E) * trace (P2 ||| E)}) :=
  (all (fun p1 => all (fun p2 => (p1.1.2 == p2.1.2) && (p1.2 == p2.2)) (support eta)) (support mu)) && (R (proj_mt_l P1 E mu) (proj_mt_l P2 E eta)).



Lemma comparable_cong {G D D' D'' : context} (P1 : PIOA G D) (P2 : PIOA G D') (P3 : PIOA G D'') :
  comparable P1 P2 -> comparable (P1 ||| P3) (P2 ||| P3).
  move/andP => [h1 h2]; apply/andP; split; apply/seq_eqmemP.
  rewrite //= => z.
  rewrite !mem_seqD !mem_cat.
  rewrite !(seq_eqmemP _ _ h1) !(seq_eqmemP _ _ h2) //=.

  rewrite //= => z; rewrite !mem_cat !(seq_eqmemP _ _ h2) //=.
Qed.

Lemma all2P {X Y : eqType} (s1 : seq X) (s2 : seq Y) (p : X -> Y -> bool) :
  reflect (forall x, x \in s1 -> forall y, y \in s2 -> p x y) (all (fun x => all (fun y => p x y) s2) s1).
  apply/(iffP idP).
  move/allP => H x Hx y Hy.
  move: (allP (H x Hx));move/(_ y Hy); done.

  move => H; apply/allP => x Hx; apply/allP => y Hy; apply H; done.
Qed.


Lemma simulation_cong {G D D' : context} (P1 P2 : PIOA G D) (E : PIOA G D') (He : env P1 E) (Hcomp : comparable P1 P2) R :
  simulation_sameh P1 P2 Hcomp R ->
  simulation_sameh (P1 ||| E) (P2 ||| E) (comparable_cong P1 P2 E Hcomp) (extension P1 P2 E He R).
  move => Rsim.
  elim (Rsim) => rs1 rs2 rs3 rs4; simpl in *.
  constructor; simpl.

  (* trace condition *)
  move => mu eta; move/andP; rewrite //=; elim.
  move/all2P; rewrite //= => H Hr p1 p2 Hp1 Hp2.
  move/andP: (H p1 Hp1 p2 Hp2); elim => _ /eqP; done.

  (* init dist *)
  apply/andP; split.
  apply/all2P; simpl => x Hx y Hy.
  rewrite /initDist in Hx; support_tac Hx.
  rewrite /initDist in Hy; support_tac Hy; subst; rewrite //= !eq_refl //=.

  have Hp: forall P, proj_mt_l P E (initDist (P ||| E)) = initDist P.
  move => c P.
  rewrite /proj_mt_l /initDist measMap_ret //=.
  rewrite !Hp //=.

  (* locally controlled action *)
  move => mu eta hc Hlhc; move/andP; elim.
  move/all2P => H; simpl in H.
  move => Hr.

  move/andP: (He); elim => He1 He2.

  destruct hc as [h | c].
  destruct h as [hl | hr].
  rewrite !hidden1P.

  apply liftingBind_dep.
  
  have Hc2: compatible P2 E.
    rewrite /compatible; elim (andP Hcomp) => _ /seq_eqmemP => Heq.
    apply/seq_disjointP => x; rewrite -Heq => Hx.
    move/seq_disjointP: He1; move/(_ _ Hx); done.
  have lc2 : locally_controlled (P2 ||| E) hc.
    move: Hlhc.
    rewrite /locally_controlled; elim hc; rewrite //=.
    move => b; rewrite !mem_cat; elim (andP Hcomp) => _ /seq_eqmemP => Heq; rewrite Heq //=.
    
  elim (compPIOAP P1 E He1 hc Hlhc mu); elim (compPIOAP P2 E Hc2 hc lc2 eta); intros; try congruence.
  admit.
  admit.
  admit.

  admit.
  rewrite 
  rewrite i0 in i2.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  `
  admit.
  congruence.
  intros. 
  rewrite e in e1; done.

  have: lifting R (act P1 hc (proj_mt_l mu)) (act P2 hc (proj


  
  admit.


  (* input trivial *)
  move => mu eta; elim (andP He); rewrite /closed //= => _ /eqP -> in_nil //=.
Admitted.



Lemma extension_rel {G D D'' : context} (P1 : PIOA G D) (P2 : PIOA G D) (E : PIOA G D'') (He : env P1 E) (Hcomp : comparable P1 P2) R g :
  protocol_for (P1 ||| E) g ->
  simulation_sameh P1 P2 Hcomp R ->
  lifting (extension P1 P2 E He R) (run (P1 ||| E) g) (run (P2 ||| E) g).

  move => Hprot.
  move => Rsim.
  elim Rsim => s1 s2 s3 s4.
  induction g using last_ind.
  rewrite /run //= .
  exists (ret (initDist (P1 ||| E), initDist (P2 ||| E))).
  apply/and3P; split.

  rewrite bindRet_l //=.
  rewrite bindRet_l //=.
  rewrite measSupport_ret.
  rewrite all_seq1 //.
  rewrite /initDist //=.

  apply/andP; split.
  rewrite !measSupport_ret !all_seq1 //= !eq_refl //=.

  rewrite /proj_mt_l /initDist !measMap_ret /proj_mt_l //=.
  rewrite !run_rcons.

  have Hprg : protocol_for (P1 ||| E) g.
    by rewrite /protocol_for all_rcons in Hprot; elim (andP Hprot) => hp1 hp2.

  elim (IHg Hprg) => m Hm.
  elim (and3P Hm) => H1 H2 H3.
  rewrite (eqP H1) (eqP H2).
  rewrite !act_bind.
  apply liftingBind_dep => x1 Hx1.

  simpl in *.
  destruct (simulation_cong P1 P2 E He Hcomp R Rsim).
  apply sim_step_lc0; clear sim_trace_eq0 sim_start0 sim_step_lc0 sim_step_i0.

  rewrite /protocol_for all_rcons in Hprot; elim (andP Hprot) => hp1 hp2.
  elim (andP He) => e1 e2; rewrite /closed in e2.
  rewrite /is_chan in hp1.
  rewrite (eqP e2) //= in hp1.

  apply/andP; split.
  apply/allP => p1 Hp1; apply/allP => p2 Hp2.
  move/allP: (H3);move/(_ x1 Hx1).
  move/andP; elim.
  move/allP/(_ p1 Hp1)/allP/(_ p2 Hp2); done.

  move/allP: H3;move/(_ x1 Hx1).
  move/andP; elim => _.
  done.
Qed.

  

Theorem simulation_sound_sameh {Gamma Delta : context} (P1 P2 : PIOA Gamma Delta) (Hcomp : comparable P1 P2) R: simulation_sameh P1 P2 Hcomp R -> refines P1 P2 Hcomp.
  move => Rsim D E He g1 Hg1.
  have chaneq: is_chan (P1 ||| E) =1 is_chan (P2 ||| E).
    elim (andP Hcomp); move/seq_eqmemP => h1; move/seq_eqmemP => h2; move => z; rewrite //=.
    case z => s; rewrite //= !mem_cat !mem_seqD !mem_cat h1 h2 //=.

  exists g1; split.
  rewrite /protocol_for.
  rewrite -(eq_all chaneq) //=.


  have Hext: lifting (extension P1 P2 E He R) (run (P1 ||| E) g1) (run (P2 ||| E) g1).
  apply (extension_rel P1 P2 E He Hcomp R g1); rewrite //=.

  destruct Hext as [mu Hmu]; simpl in *.
  elim (and3P Hmu) => Hmu1 Hmu2 Hmu3; simpl in *.
  rewrite (eqP Hmu1) (eqP Hmu2).
  rewrite !measMap_bind.
  apply measBind_eqP; rewrite //= => x Hx.
  move/allP: Hmu3; rewrite //=; move/(_ x Hx).
  move/andP; simpl; elim => H1 H2.
  destruct Rsim as [Htr _ _ _]; simpl in *.
  rewrite /proj_mt_l /proj_state_l /proj_trace_l in H2; simpl in H2.

  apply measMap_dirac_eq.
  admit.
  simpl => a b Ha Hb.
  have : (a.1.1, a.2).2 = (b.1.1, b.2).2.
  eapply Htr.
  apply H2.
  simpl.
  destruct a as [a1 a2]; destruct b as [b1 b2]; simpl.
  
  destruct 
  have -> : (a
  apply Htr.

   
  apply (measMap_dirac_eq x.1 x.2 snd).

  have Hts := Htr _ _ H2.

  
  SearchAbout measMap.
  rewrite measSupport_measMap in Hts.


  apply 

  simpl in *.

  move/and3P: Hmu.

  have: extension 
  SearchAbout all.
  rewrite chaneq.

    rewrite /is_chan //= !mem_cat !mem_seqD.
    rewrite 




  move/andP: Hcomp.
  move => x; rewrite /is_chan.
  move/andP: He; elim => e1 e2.
  rewrite /closed in e2.
  rewrite e2.
  rewrite //=.
  rewrite e2.
  
  exists g1; split.



  rewrite /protocol_for.

  move: Hcomp Hg1; clear; induction g1; rewrite //=.
  move=> Hcomp; move/andP; elim => h1 h2; apply/andP; split.
  move: h1.
  rewrite /is_chan; elim a; rewrite //=.
  move => b; rewrite !mem_cat !mem_seqD !mem_cat.
  elim (andP Hcomp); move/seq_eqmemP => c1; move/seq_eqmemP => c2.
  rewrite -!(c1 b) -!(c2 b) //=.
  apply IHg1; rewrite //=.

  have Hext: lifting (extension P1 P2 E He R) (papply (P1 ||| E) g1) (papply (P2 ||| E) g1).
  by apply (extension_rel P1 P2 E He Hcomp).




  done.






  

  have: extension P1 P2 E He R (papply (P1 ||| E) g1) (papply (P2 ||| E) g1).
  induction g1 using last_ind.
  rewrite /papply //=.
  rewrite /initDist //=.

  rewrite /extension !measSupport_ret; apply/andP; split.
  rewrite //= !eq_refl //=.
  rewrite /proj_mt_l //= !measMap_ret //=.
  rewrite !papply_rcons.
  rewrite /extension; apply/andP; split.
  case x.
  rewrite /act.


  rewrite !papply_rcons.





  Check measMap_ret.

