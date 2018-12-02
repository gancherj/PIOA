
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Premeas Meas Posrat Aux FastEnum CompPIOA Lifting Action.

Definition is_chan {Gamma D : ctx} (P : PIOA Gamma D) (hc : (H P) + (C P)) :=
  match hc with
  | inl _ => true
  | inr c =>
    c \in (inputs P ++ outputs P)
            end.
  
Definition comparable {Gamma D D' : ctx} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') := (inputs P1 ==i inputs P2) && (outputs P1 ==i outputs P2).

Definition protocol_for {Gamma D : ctx} (P : PIOA Gamma D) (x : seq (cdom D + cdom Gamma)) := all (is_chan P) x.

Definition env {Gamma D D' : ctx} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') :=
  compatible P1 P2 && closed (P1 ||| P2).
  
Definition refines  {Gamma D D' : ctx} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') (hc : comparable P1 P2) :=
  forall {D'' : ctx} (E: PIOA Gamma D''), env P1 E -> forall g1, protocol_for (P1 ||| E) g1 -> exists g2, protocol_for (P2 ||| E) g2 /\ 
        (run (P1 ||| E) (g1)) <$> snd = (run (P2 ||| E) (g2)) <$> snd.

(*

Record simulation_sameh  {Gamma D : ctx} (P1 P2 : PIOA Gamma D) (Hcomp : comparable P1 P2)
       (R : {meas (St P1) * (trace P1)} -> {meas (St P2) * (trace P2)} -> bool) :=
  {
    sim_trace_eq : forall mu eta , R mu eta -> mu <$> snd = eta <$> snd;
    sim_start : R (initDist P1) (initDist P2);
    sim_step_lc : forall mu eta (hc : (H P1) + (C P1)), locally_controlled P1 hc -> R mu eta -> lifting R (act P1 hc mu) (act P2 hc eta);
    sim_step_i : forall mu eta (a : action Gamma),
        (tag a \in inputs P1) -> R mu eta ->
        R (x <- mu; s <- app_i P1 a x.1; ret (s, x.2)) (x <- eta; s <- app_i P2 a x.1; ret (s, x.2))
                          }. 

Definition restr_l {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') (p : (St (P ||| P')) * seq (action G)) : St P * seq (action G) :=
   (p.1.1, filter (fun x => tag x \in inputs P ++ outputs P) p.2).

Definition restr_r {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') (p : (St (P ||| P')) * seq (action G)) : St P' * seq (action G) :=
   (p.1.2, filter (fun x => tag x \in inputs P' ++ outputs P') p.2).

Fixpoint reconstr_tr {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') (t1 : seq (action G)) {struct t1} := fix rec2 (t2 : seq (action G)) := 
  match t1, t2 with
  | x :: xs, y :: ys =>
    if x == y then
      x :: reconstr_tr P P' xs ys
    else if tag x \in inputs P ++ outputs P then
           x :: reconstr_tr P P' xs (y :: ys)
         else
           y :: rec2  ys
  | x :: xs, nil =>
    x :: reconstr_tr P P' xs nil
  | nil, y :: ys =>
    y :: rec2 ys
  | nil, nil => nil
                  end.

Lemma run_decomp {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') g (H : protocol_for (P ||| P') g) :
  forall p, p \in support (run (P ||| P') g) ->
                  p.2 = (reconstr_tr P P' (restr_l P P' p).2 (restr_r P P' p).2).
  induction g using last_ind.
  admit.
  simpl; intros.
  rewrite run_rcons in H0.
  rewrite /act in H0.
  destruct x.
  move/support_bindP: H0.
  elim => a [ha1 ha2].
  have hg: protocol_for (P ||| P') g.
  admit.
  move: (IHg hg _ ha1) => h.
  SearchAb

Lemma simulation_sound {G D : ctx} (P1 P2 : PIOA G D) (hc : comparable P1 P2) R :
  simulation_sameh P1 P2 hc R ->
  refines P1 P2 hc.
  case => h1 h2 h3 h4.
  move => D' E HE g Hg1.


  exists g.
  split.
  admit.

  have: (restr_l P1 E (run (P1 ||| E) g)) <$> snd = (restr_l P2 E (run (P2 ||| E) g)) <$> snd /\
        (restr_r P1 E (run (P1 ||| E) g)) = (restr_r P2 E (run (P2 ||| E) g)).
  admit.
  elim => H1 H2.
  

  have: 

  induction g using last_ind.
  admit.
  rewrite !run_rcons.

  have: 

  admit. (* easy *)


  induction g.
  rewrite /run //=.
  admit.

  rewrite /run //=.

  rewrite run_cons.
  done.
  admit.

  
  apply (h1 (run (P1 ||| E) g) (run (P2 ||| E) g)).


(*

Definition restr_trace_l {Gamma D : context} (P1 : PIOA Gamma D) (x : seq (action Gamma)) : seq (action Gamma) :=
  filter (fun a => tag a \in (inputs P1 ++ outputs P1)) x.

Notation "t |t_ P" := (restr_trace_l P t) (at level 60).

Definition restr_mt_l {Gamma D : context} {S : choiceType} (P : PIOA Gamma D) (mu : {meas ((St P) * S) * (seq (action Gamma))}) : {meas (St P) * (seq (action Gamma))} :=
  mu <$> (fun p => (p.1.1, p.2 |t_P)).

Notation "mu |m_ P" := (restr_mt_l P mu) (at level 60).

Lemma restr_bind {Gamma D : context} {A S : choiceType} (P : PIOA Gamma D) (c1 : {meas A}) (c2 : A -> {meas ((St P) * S) * (seq (action Gamma))})  :
  (x <- c1; c2 x) |m_ P = (x <- c1; (c2 x) |m_ P).
rewrite /restr_mt_l measMap_bind; simpl; done.
Qed.

Definition extension {Gamma D D' D'' : context} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') (E : PIOA Gamma D'') 
           (R : {meas (St P1 * trace P1)} -> {meas (St P2 * trace P2)} -> bool)
           (mu : {meas St (P1 ||| E) * trace (P1 ||| E)})
           (eta : {meas St (P2 ||| E) * trace (P2 ||| E)}) :=
  (all (fun p => all (fun q => (p.2 == q.2) && (p.1.2 == q.1.2)) (support eta)) (support mu)) &&
  R (mu |m_ P1) (eta |m_ P2).

Lemma extensionP {Gamma D D' D'' : context} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') (E : PIOA Gamma D'') 
           (R : {meas (St P1 * trace P1)} -> {meas (St P2 * trace P2)} -> bool)
           (mu : {meas St (P1 ||| E) * trace (P1 ||| E)})
           (eta : {meas St (P2 ||| E) * trace (P2 ||| E)})
           (Hmu : mass mu != 0)
           (Heta : mass eta != 0)
  :
  (extension P1 P2 E R mu eta) -> (exists u v e tau, [/\ (mu = ((u ** (ret e)) ** (ret tau))), (eta = ((v ** (ret e)) ** (ret tau))) & R (u ** (ret tau|t_P1)) (v ** (ret tau|t_P2))]). 
  move/andP; elim => h1 h2; simpl in *.
  move/all2P: h1 => h1; simpl in h1.

  elim (mass_neq0 _ Hmu) => xmu Hxmu.
  elim (mass_neq0 _ Heta) => xeta Hxeta.

  have h3 : forall x y, x \in support mu -> y \in support mu -> (x.2 = y.2) /\ (x.1.2 = y.1.2).
    intros.
    move/andP: (h1 _ H _ Hxeta); elim.
    move/andP: (h1 _ H0 _ Hxeta); elim.
    move/eqP => -> /eqP <- /eqP -> /eqP ->; done.

  have h4 : forall x y, x \in support eta -> y \in support eta -> (x.2 = y.2) /\ (x.1.2 = y.1.2).
    intros.
    move/andP: (h1 _ Hxmu _ H); elim.
    move/andP: (h1 _ Hxmu _ H0); elim.
    move/eqP => -> /eqP <- /eqP -> /eqP ->; done.

  exists (mu <$> (fun p => p.1.1)), (eta <$> (fun p => p.1.1)), (xmu.1.2), (xmu.2).

  split; simpl in *.


  apply prod_dirac_Pr; simpl; first by move => x Hx; elim (h3 _ _ Hxmu Hx).
  symmetry; apply prod_dirac_Pr; simpl.
  move => x; rewrite measMapE.
  move/support_bind; elim => y [Hy1 Hy2]; rewrite support_ret in Hy2.
  rewrite mem_seq1 in Hy2; rewrite (eqP Hy2).
  elim (h3 _ _ Hy1 Hxmu); done.

  rewrite measMap_measMap; done.

  
  apply prod_dirac_Pr; simpl; first by move => x Hx; elim (andP (h1 _ Hxmu _ Hx)); move/eqP ->.
  symmetry; apply prod_dirac_Pr; simpl.
  move => x; rewrite measMapE.
  move/support_bind; elim => y [Hy1 Hy2]; rewrite support_ret in Hy2.
  rewrite mem_seq1 in Hy2; rewrite (eqP Hy2).
  elim (andP (h1 _ Hxmu _ Hy1)) => _ /eqP ->; done.

  rewrite measMap_measMap; done.

  have -> : ((mu <$> (fun p : St P1 * St E * seq {i : cdom Gamma & Gamma i} => p.1.1)) **
     (ret xmu.2 |t_ P1)) = (mu |m_ P1).
  rewrite /restr_mt_l //=.
  symmetry; apply prod_dirac_Pr; simpl.
  move => x Hx.
  rewrite measMapE in Hx; move/support_bind: Hx; elim => y [Hy1 Hy2].
  rewrite support_ret mem_seq1 in Hy2; move/andP: Hy2; elim => _ /eqP ->; simpl.
  elim (h3 _ _ Hxmu Hy1) => ->; done.

  rewrite measMap_measMap; done.

  have -> : ((eta <$> (fun p : St P2 * St E * seq {i : cdom Gamma & Gamma i} => p.1.1)) **
     (ret xmu.2 |t_ P2)) = (eta |m_ P2).
  rewrite /restr_mt_l //=.
  symmetry; apply prod_dirac_Pr; simpl.
  move => x Hx.
  rewrite measMapE in Hx; move/support_bind: Hx; elim => y [Hy1 Hy2].
  rewrite support_ret mem_seq1 in Hy2; move/andP: Hy2; elim => _ /eqP ->; simpl.
  move/andP: (h1 _ Hxmu _ Hy1); elim => /eqP <-; done .
  rewrite measMap_measMap; done.
  done.
Qed.


Lemma comparable_cong {G D D' D'' : context} (P1 : PIOA G D) (P2 : PIOA G D') (P3 : PIOA G D'') :
  comparable P1 P2 -> comparable (P1 ||| P3) (P2 ||| P3).
  move/andP => [h1 h2]; apply/andP; split; apply/seq_eqmemP.
  rewrite //= => z.
  rewrite !mem_seqD !mem_cat.
  rewrite !(seq_eqmemP _ _ h1) !(seq_eqmemP _ _ h2) //=.

  rewrite //= => z; rewrite !mem_cat !(seq_eqmemP _ _ h2) //=.
Qed.

  

Lemma extension_projK {G D D' : context} (P1 P2 : PIOA G D) (E : PIOA G D') (R : _ -> _ -> bool)  mu eta Hc :
  simulation_sameh P1 P2 Hc R ->
  (forall x y, x \in support mu -> y \in support eta -> 
                                 x.2|t_P1 = y.2|t_P2-> (x.2 == y.2) && (x.1.2 == y.1.2)) ->
  R (mu |m_P1) (eta |m_P2) ->
  (extension P1 P2 E R) mu eta.

  move => HR H1 H2; apply/andP; split; simpl.
  apply/all2P => x Hx y Hy; simpl in *.
  apply H1.
  done.
  done.
  case HR => h1 h2 h3 h4; simpl in *.

  elim (h1 _ _ H2) => u; elim => v; elim => tau; elim => h5 h6.

  have Hx1: (x.1.1, x.2 |t_P1) \in support (mu |m_ P1).
  rewrite /restr_mt_l measMapE; apply/ support_bind; exists x; split; rewrite //=.
  rewrite support_ret mem_seq1; done.

  have Hy1: (y.1.1, y.2 |t_P2) \in support (eta |m_ P2).
  rewrite /restr_mt_l measMapE; apply/ support_bind; exists y; split; rewrite //=.
  rewrite support_ret mem_seq1; done.

  rewrite h5 support_measProd support_ret allpairs_seq1 in Hx1.
  elim (mapP Hx1) => x0 _ Heq; injection Heq => -> _.

  rewrite h6 support_measProd support_ret allpairs_seq1 in Hy1.
  elim (mapP Hy1) => y0 _ Heq1; injection Heq1 => -> _; done.

  done.
Qed.

Lemma lifting_bind_l {A B : choiceType} (mu : {meas A}) (eta : {meas B}) (f1 : A -> {meas A}) (f2 : B -> {meas B}) R : lifting R mu eta -> (forall x y, x \in support mu -> y \in support eta -> lifting R (f1 x) (f2 y)) -> lifting R (x <- mu; f1 x) (x <- eta; f2 x).
  admit.
Admitted.

Check isLifting.

Lemma extension_lift {G D D' : context} (P1 P2 : PIOA G D) (E : PIOA G D') (R : _ -> _ -> bool)
      mu eta l Hc :
  simulation_sameh P1 P2 Hc R ->
  (forall p x y, p \in support l -> x \in support p.1 -> y \in support p.2 ->
                                 proj_trace_l P1 E x.2 = proj_trace_l P2 E y.2 -> (x.2 == y.2) && (x.1.2 == y.1.2)) ->
  isLifting R (proj_mt_l P1 E mu) (proj_mt_l P2 E eta) l ->
  lifting (extension P1 P2 E R) mu eta.
  


Lemma simulation_cong {G D D' : context} (P1 P2 : PIOA G D) (E : PIOA G D') (He : env P1 E) (Hcomp : comparable P1 P2) R :
  simulation_sameh P1 P2 Hcomp R ->
  simulation_sameh (P1 ||| E) (P2 ||| E) (comparable_cong P1 P2 E Hcomp) (extension P1 P2 E R).
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

  destruct hc as [[hl | hr] | c].
  (* hidden on P1, p2 *)
  rewrite !hidden1P.

  
  have E_mu_eta : lifting (extension P1 P2 E R) mu eta.
  exists (ret (mu, eta)); apply/and3P; split.
  rewrite bindRet_l //=.
  rewrite bindRet_l //=.
  rewrite support_ret all_seq1 //=.
  apply/andP; split.
  apply/all2P => x Hx y Hy; simpl in *.
  apply H; done.
  done.


  apply lifting_bind_l.
  done.

  simpl => x y Hx Hy.
  

  apply id_lifting; apply/andP; split.
  simpl; apply/all2P => a Ha b Hb; simpl in *.


  admit.
  admit.

  admit.

  admit.
  elim (andP He); rewrite /closed => _ /eqP //= => -> ? ? ? ; rewrite in_nil; done.
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

*)

*)