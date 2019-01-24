
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Premeas Meas Posrat Aux FastEnum CompPIOA Closure Action.

  
Definition comparable {Gamma D D' : ctx} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') := (inputs P1 ==i inputs P2) && (outputs P1 ==i outputs P2).

Definition env {Gamma D D' : ctx} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') :=
  compatible P1 P2 && closed (P1 ||| P2).

Definition closed_refine {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') (hc : comparable P P') :=
  forall g, valid_chanseq P g -> exists g', valid_chanseq P' g' /\ (run P g <$> snd = run P' g' <$> snd).

Lemma comparable_comp_r {G D D' D'' : ctx} {P : PIOA G D} {P' : PIOA G D'} (E : PIOA G D'') (hc : comparable P P') : comparable (P ||| E) (P' ||| E).
  elim (andP hc); move/seq_eqmemP => h1; move/seq_eqmemP => h2.
  apply/andP; split.
  simpl.
  apply/seq_eqmemP => x.
  rewrite !mem_seqD !mem_cat !h1 !h2 //=.
  apply/seq_eqmemP => x; rewrite !mem_cat !h2 //=.
Qed.
  
Definition refines  {Gamma D D' : ctx} (P1 : PIOA Gamma D) (P2 : PIOA Gamma D') (hc : comparable P1 P2) :=
  forall {D'' : ctx} (E: PIOA Gamma D''), env P1 E -> closed_refine (P1 ||| E) (P2 ||| E) (comparable_comp_r _ hc).

(* various lemms *)
Lemma valid_pchan_comp {G D D' : ctx} (P : PIOA G D) (E : PIOA G D') (he : env P E) x :
  valid_pchan (P ||| E) (inr x) = (x \in outputs P) || (x \in outputs E).
  rewrite /valid_pchan //=.
  rewrite mem_cat //= .
Qed.

Lemma valid_pchan_compare {G D : ctx} (P P' : PIOA G D) (hc : comparable P P') :
    valid_pchan P =1 valid_pchan P'.
    case; simpl.
    done.
    elim (andP hc).
    move => _ /seq_eqmemP => h; intro; rewrite h //=.
Qed.


Lemma comparable_sym {G D : ctx} (P P' : PIOA G D) :
  comparable P P' = comparable P' P.
  apply Bool.eq_true_iff_eq; split; rewrite /comparable; move/andP; elim; move/seq_eqmemP => h1; move/seq_eqmemP => h2; apply/andP; split; apply/seq_eqmemP => x; rewrite ?h1 ?h2 //=.
Qed.


Lemma comparable_compatible_l {G D D' D'' : ctx} (P : PIOA G D) (P' : PIOA G D') (E : PIOA G D'') :
  comparable P P' -> compatible P E -> compatible P' E.
  move/andP; elim; move/seq_eqmemP => h1; move/seq_eqmemP => h2; rewrite /compatible.
  move/seq_disjointP => H; apply/seq_disjointP => x.
  rewrite -h2 //=; apply H.
Qed.


Section InternalSim.
  Context {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') (hc : comparable P P').
  Context (ccorr : C P -> (seq (H P') * C P' * seq (H P'))).
  Context (hcorr : H P -> seq (H P')).

  Context (h_ccorr : forall c, c \in outputs P -> (ccorr c).1.2 \in outputs P').

  Definition seq_ccorr (c : C P) : seq (cdom D' + cdom G) :=
    (map inl (ccorr c).1.1) ++ (inr (ccorr c).1.2 :: (map inl (ccorr c).2)).

  Definition seq_hcorr (h : H P) : seq (cdom D' + cdom G) := map inl (hcorr h).

  Record InternalSim (R : {meas (St P) * trace P} -> {meas (St P') * trace P'} -> bool) :=
    {
      int_sound : forall mu eta, mvalid P mu -> mvalid P' eta -> R mu eta -> mu <$> snd = eta <$> snd;
      int_start : R (initDist P) (initDist P');
      int_stepv : forall mu eta c, c \in outputs P ->
                                         mvalid P mu ->
                                         mvalid P' eta ->
                                         R mu eta ->
                                         closure R (act P (inr c) mu) (runFrom P' (seq_ccorr c) eta);
      int_steph : forall mu eta h,
          mvalid P mu ->
          mvalid P' eta ->
          R mu eta ->
          closure R (act P (inl h) mu) (runFrom P' (seq_hcorr h) eta)
                                           }.

  Lemma InternalSim_sound R : InternalSim R ->  closed P -> 
                              closed_refine P P' hc.
    case => h1 h2 h3 h4 cl1.

    have: forall g1, valid_chanseq P g1 -> exists g2, valid_chanseq P' g2 /\ closure R (run P g1) (run P' g2).

    induction g1 using last_ind.
    move => _; exists nil.
    simpl.
    rewrite /run //=.
    split.
    done.
    apply id_closure.
    apply isdist_ret.
    apply isdist_ret.
    done.



    rewrite /valid_chanseq all_rcons; move/andP; elim => hg1 hg2.
    destruct x as [h | c].
    elim (IHg1 hg2) => g' Hg' {IHg1}.
    destruct Hg' as [IH1 IH2].
    exists (g' ++ (seq_hcorr h)); split.
    rewrite all_cat; apply/andP; split.
    done.
    rewrite all_map; induction (hcorr h); done.
    rewrite run_rcons run_cat.
    rewrite runFrom_mkbind act_mkbind.

    destruct IH2; simpl in *.
    move/and3P: H; elim => H1 H2 H3; simpl in *.
    rewrite (eqP H1) (eqP H2); msimp.
    apply closure_bind; simpl => X HX.
    move/and3P: (allP H3 _ HX); elim => H4 H5 H6.
    rewrite -runFrom_mkbind.
    apply h4.

    split.
    simpl => x0 Hx0; have: x0 \in support (run P g1).
    rewrite (eqP H1); apply/support_bindP; exists X; split; done.
    intro.
    have: mvalid P (run P g1) by apply run_mvalid.
    elim.
    move/(_ _ x1); done.
    done.

    split.
    simpl => x0 Hx0; have: x0 \in support (run P' g').
    rewrite (eqP H2); apply/support_bindP; exists X; split; done.
    intro.
    have: mvalid P' (run P' g') by apply run_mvalid.
    elim.
    move/(_ _ x1); done.
    done.
    done.


    elim (IHg1 hg2) => g' Hg' {IHg1}.
    destruct Hg' as [IH1 IH2].
    exists (g' ++ (seq_ccorr c)); split.
    rewrite all_cat; apply/andP; split; rewrite //=.
    rewrite /seq_ccorr all_cat all_cons ?andbT.
    rewrite all_map; induction (ccorr c).1.1; done.
    simpl.
    by apply h_ccorr.


    rewrite all_map; induction (ccorr c).2; done.

    rewrite run_rcons run_cat act_mkbind runFrom_mkbind.
    elim IH2 => L; move/and3P; elim => Hl1 Hl2 Hl3; simpl in *.
    rewrite (eqP Hl1) (eqP Hl2); msimp; apply closure_bind.
    simpl => x Hx.

    rewrite -runFrom_mkbind.
    apply h3.
    done.
    split.
    simpl => x0 Hx0.
    have: x0 \in support (run P g1).
    rewrite (eqP Hl1); apply/support_bindP; exists x; split; done.
    intro.
    have: mvalid P (run P g1) by apply run_mvalid.
    elim => H _.
    apply H; done.

    move/and3P: (allP Hl3 _ Hx); elim; done.

    split.
    intros.
    have: mvalid P' (run P' g') by apply run_mvalid.
    elim => H' _; apply H'.
    rewrite (eqP Hl2); apply/support_bindP; exists x; split; done.
    move/and3P: (allP Hl3 _ Hx); elim; done.
    move/and3P: (allP Hl3 _ Hx); elim; done.



    move => H g Hg.
    elim (H g Hg) => g'; exists g'; split.
    elim H0; done.
    apply eq_closure; simpl.
    apply closure_fmap; simpl.
    destruct H0.
    destruct H1; simpl in *.
    move/and3P: H1 => [H11 [H12 H13]].
    exists x; apply/and3P; split.
    done.
    done.
    apply/allP => y Hy.
    elim (and3P (allP H13 _ Hy)); intros; apply/and3P; split.
    done.
    done.
    apply/eqP; apply h1.

    split.
    intros; have: mvalid P (run P g) by apply run_mvalid.
    elim => H' _.
    apply H'.
    rewrite (eqP H11); apply/support_bindP.
    exists y; split; done.
    done.

    split.
    intros; have: mvalid P' (run P' g') by apply run_mvalid.
    elim => H' _.
    apply H'.
    rewrite (eqP H12); apply/support_bindP.
    exists y; split; done.
    done.
    done.
 Qed.
End InternalSim.
