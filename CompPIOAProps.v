
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum finmap.

Require Import PIOA Meas Posrat CompPIOA StateSim Premeas Aux FastEnum.

Section CompPIOA_symm.
  Context {A : finType}.
  Context (P1 P2 : @PIOA A).
  Context (Hc : compatible P1 P2).
  Context (hclosed : closed (CompPIOA P1 P2 Hc)).

  Lemma compat_sym : compatible P2 P1.
    move/and4P: Hc; elim => h1 h2 h3 h4.
    apply/and4P; split.
    apply/all_fsetP => C HC; apply/all_fsetP => C' HC'.
    move/all_fsetP: h1; move/(_ C' HC'); move/all_fsetP/(_ C HC); rewrite eq_sym fdisjoint_sym //=.

    apply/all_fsetP => C HC; apply/all_fsetP => C' HC'; move/all_fsetP: h2; move/(_ C' HC')/all_fsetP/(_ C HC); rewrite fdisjoint_sym //=.

    apply/all_fsetP => C HC; apply/all_fsetP => C' HC'; move/all_fsetP: h4; move/(_ C' HC')/all_fsetP/(_ C HC); rewrite fdisjoint_sym //=.
    apply/all_fsetP => C HC; apply/all_fsetP => C' HC'; move/all_fsetP: h3; move/(_ C' HC')/all_fsetP/(_ C HC); rewrite fdisjoint_sym //=.
  Qed.


  Lemma sym_closed : closed (CompPIOA P2 P1 compat_sym).
    have H := hclosed.
    rewrite /closed //= in H.
    rewrite /closed //= (fsetUC) (fsetUC (cO P2)) //=.
  Qed.


  Lemma compPIOA_sym : refinement (CompPIOA P1 P2 _) (CompPIOA P2 P1 compat_sym) hclosed sym_closed. 
    eapply simpleStateSound; instantiate (1 := fun p => (p.2, p.1)); constructor; rewrite //=.
    rewrite (fsetUC (cI P2)) (fsetUC (cO P2)) //=.
    rewrite fsetUC //=.
    rewrite fsetUC //=.
    move => a s.
    destruct (tr P2 s.2 a); destruct (tr P1 s.1 a); rewrite //=.
    rewrite measMap_bind measBind_swap; congr (Some _); apply measBind_eqP => x0 Hx0; rewrite measMap_bind //=; apply measBind_eqP => y Hy; rewrite measMap_ret //=.
    remember (a \in actions P1) as b; destruct b; rewrite -Heqb //=.
    congr (Some _); rewrite measMap_bind; apply measBind_eqP => x Hx; rewrite measMap_ret //=.

    remember (a \in actions P2) as b; destruct b; rewrite -Heqb //=.
    congr (Some _); rewrite measMap_bind; apply measBind_eqP => x Hx; rewrite measMap_ret //=.
  Qed.    
End CompPIOA_symm.

(* TODO tedious *)
Lemma compatible_assoc_r {A} (P1 P2 P3 : @PIOA A) (Hc1 : compatible P2 P3) (Hc2 : compatible P1 (CompPIOA P2 P3 Hc1)) : exists (Hc3 : compatible P1 P2), compatible (CompPIOA P1 P2 Hc3) P3.
  have: compatible P1 P2.
  elim (and4P Hc1) => h1 h2 h3 h4.
  elim (and4P Hc2) => h5 h6 h7 h8.
  apply/and4P; split.
  apply/all_fsetP => C Hc; apply/all_fsetP => C' Hc'.
  have: C' \in channels (CompPIOA P2 P3 Hc1).
  rewrite /channels //=.
  move/fsetUP: Hc'; elim.
  move/fsetUP; elim.
  remember (C' \in (cO P2 `|` cO P3)%fset) as b; destruct b.
  move => _; apply/fsetUP; left; apply/fsetUP; right; done.
  move => H; apply/fsetUP; left; apply/fsetUP; left; apply/fsetDP; split.
  apply/fsetUP; left; done.
  rewrite -Heqb //=.
  move => H; apply/fsetUP; left; apply/fsetUP; right; apply/fsetUP; left; done.
  move => H; apply/fsetUP; right; apply/fsetUP; left; done.
  move=> C'in.
  move/all_fsetP: h5; move/(_ C Hc);move/all_fsetP/(_ C').
  rewrite C'in.
  move/(_ is_true_true); rewrite //=.

  apply/all_fsetP => C Hc; apply/all_fsetP => C' Hc'.
  admit.
  admit.
  admit.
  intro H; exists H.
  admit.
Admitted.

Section CompPIOA_assoc.
  Context {A : finType}.
  Context (P1 P2 P3 : @PIOA A).
  Context (Hc1 : compatible P2 P3).
  Context (Hc2 : compatible P1 (CompPIOA P2 P3 Hc1)).

  Context (ic : closed (CompPIOA P1 (CompPIOA P2 P3 Hc1) Hc2)).

  Lemma hc12: compatible P1 P2.
    destruct (compatible_assoc_r _ _ _ Hc1 Hc2).
    apply x.
  Qed.

  Lemma hc12_3 : compatible (CompPIOA P1 P2 hc12) P3. 
    destruct (compatible_assoc_r _ _ _ Hc1 Hc2).
    have: x = hc12.
    apply bool_irrelevance.
    move => <- ;rewrite //=.
  Qed.

  Lemma assoc_input_eq : cI (CompPIOA (CompPIOA P1 P2 hc12) P3 hc12_3) = cI (CompPIOA P1 (CompPIOA P2 P3 Hc1) Hc2).
    rewrite //=.
    apply/fsetP => x; rewrite !in_fsetD !in_fsetU !in_fsetD !in_fsetU !negb_or.
    case (x \in cO P1); case (x \in cO P2); case (x \in cO P3); case (x \in cI P1); case (x \in cI P2); case (x \in cI P3); rewrite //=.
  Qed.

  Lemma assoc_output_eq : cO (CompPIOA (CompPIOA P1 P2 hc12) P3 hc12_3) = cO (CompPIOA P1 (CompPIOA P2 P3 Hc1) Hc2).
    rewrite //=.
    apply/fsetP => x; rewrite !in_fsetU //=.
    remember (x \in cO P1) as b1; rewrite -Heqb1; destruct b1;
    remember (x \in cO P2) as b2; rewrite -Heqb2; destruct b2;
    remember (x \in cO P3) as b3; rewrite -Heqb3; destruct b3; rewrite //=.
  Qed.

  Lemma assoc_hidden_eq : cH (CompPIOA (CompPIOA P1 P2 hc12) P3 hc12_3) = cH (CompPIOA P1 (CompPIOA P2 P3 Hc1) Hc2).
    rewrite //=.
    apply/fsetP => x; rewrite !in_fsetU //=.
    remember (x \in cH P1) as b1; rewrite -Heqb1; destruct b1;
    remember (x \in cH P2) as b2; rewrite -Heqb2; destruct b2;
    remember (x \in cH P3) as b3; rewrite -Heqb3; destruct b3; rewrite //=.
  Qed.


  Lemma closed_assoc_r : closed (CompPIOA (CompPIOA P1 P2 hc12) P3 hc12_3).
    rewrite /closed.
    have h1 := assoc_input_eq; rewrite //= in h1.
    rewrite //= h1 //=.
  Qed.

  Lemma assocPIOA_r : refinement (CompPIOA P1 (CompPIOA P2 P3 Hc1) Hc2) (CompPIOA (CompPIOA P1 P2 hc12) P3 hc12_3) ic closed_assoc_r.
    eapply simpleStateSound.
    instantiate (1 := fun p => ((p.1, p.2.1), p.2.2)).
    constructor.
    rewrite assoc_input_eq //=.
    rewrite assoc_output_eq //=.
    rewrite assoc_hidden_eq //=.
    rewrite //=.
    move => a s.
    rewrite //=.

    Set Printing All.
    remember (tr P1 s.1 a) as o1; rewrite -Heqo1; destruct o1;
    remember (tr P2 s.2.1 a) as o2; rewrite -Heqo2; destruct o2;
    remember (tr P3 s.2.2 a) as o3; rewrite -Heqo3; destruct o3;
      rewrite //=.
    congr (Some _); rewrite measMap_bind bindAssoc.
    apply measBind_eqP => x Hx; rewrite measMap_bind !bindAssoc.
    apply measBind_eqP => y Hy; rewrite bindAssoc measBind_swap.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
  Admitted.
End CompPIOA_assoc.
