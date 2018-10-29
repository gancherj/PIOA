
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum finmap.

Require Import PIOA Meas Posrat CompPIOA.

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
    admit.
  Admitted.
End CompPIOA_symm.

Section CompPIOA_assoc.
  Context {A : finType}.
  Context (P1 P2 P3 : @PIOA A).
  Context (Hc1 : Compatible P2 P3).
  Context (Hc2 : Compatible P1 (compPIOA P2 P3 Hc1)).
  Context (Hc3 : Compatible P1 P2).
  Context (Hc4 : Compatible (compPIOA P1 P2 Hc3) P3).
  Context (ic : inputClosed (compPIOA (compPIOA P1 P2 Hc3) P3 Hc4)).

  Definition Q1 := compPIOA P1 (compPIOA P2 P3 Hc1) Hc2.
  Definition Q2 := compPIOA (compPIOA P1 P2 Hc3) P3 Hc4.


  Lemma pI_comp_assoc : pI Q1 = pI Q2.
    simpl.
    rewrite !fsetUA.
    apply fset_ext => x.
    rewrite !in_fsetD.
    rewrite !in_fsetU.
    rewrite !in_fsetD.
    rewrite !in_fsetU.
    caseOn (x \in cover (pTO P1 `|` pTO P2 `|` pTO P3)).
    intro Heq; rewrite Heq !andbF; done.
    intro Heq; rewrite Heq !andbT.
    rewrite !coverU !in_fsetU !negb_or in Heq.
    move/andP: Heq; elim; move/andP; elim; intros.
    rewrite !coverU !in_fsetU.
    rewrite (negbTE H) (negbTE H0) (negbTE H1) //=.
    rewrite !andbT.
    rewrite orbA //=.
  Qed.

  Lemma inputClosed_assoc : inputClosed (compPIOA P1 (compPIOA P2 P3 Hc1) Hc2).
    rewrite /inputClosed.
    rewrite pI_comp_assoc.
    apply ic.
  Qed.

  Lemma compPIOA_assoc : @refinement _ Q2 Q1 ic inputClosed_assoc 0.
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