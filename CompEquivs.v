
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Aux PIOA Ascii String CompPIOA SSRString FastEnum Action Refinement StateSim Compute PIOAOps.

Section CompSymm.
  Context {G D D' : ctx} (P1 : PIOA G D) (P2 : PIOA G D') (hcompat : compatible P1 P2).

  Definition p2p1 := (changeH (P2 ||| P1) (ctx_plus_symm _ _)).
  Lemma comp_comparable : comparable (P1 ||| P2) p2p1.
    apply/andP; split; simpl; apply/seq_eqmemP => x.
    rewrite !mem_seqD !mem_cat.
    rewrite (orbC (x \in inputs P1)) (orbC (x \in outputs P1)) //=.
    rewrite !mem_cat orbC //=.
  Qed.

  Lemma ssi_compsymm : refines (P1 ||| P2) p2p1 comp_comparable.
    eapply ssi_refines.
    instantiate (1 := fun p => (p.2, p.1)); constructor.
    done.
    intros; rewrite /p2p1 appv_changeh.
    simpl in H; rewrite mem_cat in H; move/orP: H; elim => co.
    caseOn (c \in inputs P2) => ci.
    rewrite app_v_comp_l_int; rewrite //=.
    rewrite app_v_comp_r_int; rewrite //=.
    rewrite !measE.
    apply mbind_eqP => y Hy.
    destruct y as [y1 y2]; destruct y2; rewrite measE.
    munder (rewrite measE); done.
    done.
    done.
    rewrite compatible_symm //=.
    rewrite app_v_comp_l_ext; rewrite //=.
    rewrite app_v_comp_r_ext //=.
    rewrite !measE; munder (rewrite measE).
    done.
    rewrite compatible_symm //=.
    caseOn (c \in inputs P1) => ci.
    rewrite (app_v_comp_l_int P2 P1) //=.
    rewrite (app_v_comp_r_int P1 P2) //=.
    rewrite !measE; apply mbind_eqP => y Hy; destruct y as [y0 y1]; destruct y1.
    rewrite measE; munder (rewrite measE).
    done.
    rewrite measE //=.
    rewrite compatible_symm //=.
    rewrite (app_v_comp_l_ext P2 P1) //=.
    rewrite (app_v_comp_r_ext P1 P2) //=.
    rewrite measE; munder (rewrite measE); done. 
    done.
    by rewrite compatible_symm //=.
    move => x h.
    rewrite apph_changeh.
    simpl.
    destruct h.
    rewrite (app_h_comp_l P1 P2) (app_h_comp_r).
    rewrite !measE //=.
    munder (rewrite measE).
    done.
    rewrite app_h_comp_l app_h_comp_r.
    rewrite measE //=.
    munder (rewrite measE).
    done.
    move => x i Hi.
    rewrite /p2p1 appi_changeh.
    simpl in Hi.
    move/seqDP: Hi; elim => h1 h2.
    rewrite mem_cat negb_or in h2; move/andP: h2 => [h21 h22].
    rewrite mem_cat in h1.
    move/enum_orP: h1; elim; move/andP; elim => h11 h12.
    rewrite app_i_comp_l //=.
    rewrite app_i_comp_r //=.
    msimp.
    done.
    rewrite app_i_comp_r //=. 
    rewrite app_i_comp_l //=. 
    msimp; done.
    rewrite app_i_comp_lr //=.
    rewrite app_i_comp_lr //=.
    rewrite mbind_swap; msimp; done.
  Qed.
End CompSymm.

Section CompAssoc.
  Context {G D D' D'' : ctx} (P1 : PIOA G D) (P2 : PIOA G D') (P3 : PIOA G D'')
          (hcompat1 : compatible P2 P3)
          (hcompat : compatible P1 (P2 ||| P3)).
  Lemma compat_assoc : compatible (P1 ||| P2) P3.
    move/seq_disjointP: hcompat => H.
    apply/seq_disjointP => x Hx.
    simpl in H.
    rewrite //= mem_cat in Hx.
    elim: (orP Hx) => in1.
    move: (H _ in1); rewrite mem_cat negb_or; move/andP; elim; done.
    move/seq_disjointP: hcompat1 => H1.
    move: (H1 _ in1); done.
  Qed.

  Definition p12_3 :=
    changeH ((P1 ||| P2) ||| P3) (ctx_plus_assoc _ _ _).

  Lemma comparable_assoc :
    comparable (P1 ||| (P2 ||| P3)) p12_3.
    apply/andP; split; rewrite /p12_3 //=.
    apply/seq_eqmemP => x.
    rewrite !mem_seqD !mem_cat.
    rewrite !negb_or !mem_seqD !mem_cat !negb_or.
    remember (x \in inputs P1) as xi1; destruct xi1; rewrite -?Heqxi1;
    remember (x \in outputs P1) as xi1; destruct xi1; rewrite -?Heqxi1;
    remember (x \in inputs P2) as xi2; destruct xi2; rewrite -?Heqxi2;
    remember (x \in outputs P2) as xi2; destruct xi2; rewrite -?Heqxi2;
    remember (x \in inputs P3) as xi3; destruct xi3; rewrite -?Heqxi3;
    remember (x \in outputs P3) as xi3; destruct xi3; rewrite -?Heqxi3; done.
    apply/seq_eqmemP => x.
    rewrite !mem_cat orbA //=.
  Qed.

  Lemma comp_assoc :
    refines (P1 ||| (P2 ||| P3)) p12_3 comparable_assoc.
    eapply ssi_refines.
    instantiate (1 := fun p => ((p.1, p.2.1), p.2.2)); constructor.
    done.
    move => x c Hc.
    rewrite appv_changeh.
    simpl in Hc; rewrite !mem_cat in Hc; move/or3P: Hc; elim.
    move => co1.
    caseOn (c \in inputs (P2 ||| P3)).
    move/seqDP; elim; rewrite mem_cat; move/orP; elim.
    move => ci2.
    rewrite mem_cat negb_or; move/andP; elim => co2 co3.
    rewrite (app_v_comp_l_int P1 (P2 ||| P3)) //=.
    rewrite (app_v_comp_l_int (P1 ||| P2) P3); rewrite //=.
    rewrite (app_v_comp_l_int P1 P2); rewrite //=.
    rewrite !measE.
    apply/mbind_eqP => y Hy; destruct y as [y0 y1]; destruct y1.
    caseOn (c \in inputs P3) => ci3.
    rewrite app_i_comp_lr; rewrite //=.
    rewrite !measE; apply mbind_eqP => a Ha; rewrite !measE.
    apply mbind_eqP => b Hb; rewrite !measE //=.
  Admitted.
End CompAssoc.