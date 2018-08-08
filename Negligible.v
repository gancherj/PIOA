
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.

Require Import Posrat.

Definition negligible (eps : posrat -> posrat) := forall (c : nat), exists (k0 : posrat), forall (k : posrat),
        k != 0 -> (Posrat 2%:Q is_true_true) < k -> k0 <= k -> (eps k) < (1 / (k ^+ c)).

Definition negligible_add e1 e2 : negligible e1 -> negligible e2 -> negligible (fun x => e1 x + e2 x).
  rewrite /negligible; intros.
  destruct (H (S c)); clear H.
  destruct (H0 (S c)); clear H0.
  exists (x + x0).
  intros.
  apply ple_add_is_le in H3; move/andP: H3 => [h01 h02].

  have H11 := H1 k H0 H2 h01; clear H1.
  have H12 := H k H0 H2 h02; clear H.
  rewrite pexp_S in H11.
  rewrite pexp_S in H12.
  eapply plt_trans.
  apply plt_add.
  apply H11.
  apply H12.
  rewrite padd2.
  rewrite -(pmulr1 (1 / k ^+ c)).
  have: Posrat (intr 2) is_true_true * (1 / (k * k ^+ c)) =
        (Posrat (intr 2) is_true_true / k) * (1 / k ^+ c).
  {

    rewrite pmulrA.
    rewrite pmulr1.
    rewrite pmul_div.
    rewrite pmulr1.
    done.
}
  intro.
  rewrite x1.
  rewrite pmulrC.
  apply plt_mulr.
  apply pdiv_neq0.
  done.
  apply pexp_neq0; done.
  apply pdiv_lt1.
  done.
  done.
Qed.
