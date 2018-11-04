
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum.

Definition compatible {A : choiceType} (P1 P2 : @PIOA A) :=
  [&& (all_fset (fun c1 => all_fset (fun c2 => (c1 == c2) || [disjoint c1 & c2]%fset) (channels P2)) (channels P1)) ,
   (all_fset (fun c1 => all_fset (fun c2 => [disjoint c1 & c2]%fset) (cO P2)) (cO P1)) , 
   (all_fset (fun c1 => all_fset (fun c2 => [disjoint c1 & c2]%fset) (channels P2)) (cH P1)) &
   (all_fset (fun c1 => all_fset (fun c2 => [disjoint c1 & c2]%fset) (cH P2)) (channels P1)) ].

Lemma compat_disjoint_c_hiddens2 {A} (P1 P2 : @PIOA A) (H : compatible P1 P2) cs :
  (cs `<=` channels P1)%fset -> [disjoint (cover cs) & (hiddens P2)]%fset.
  move=> Hsub.
  apply/fdisjointP => x Hx1.
  apply/bigfcupP; elim => y Hc1 Hc2.

  move/and4P: H; elim => [_ _ _ /all_fsetP H].

  move/bigfcupP: Hx1; elim => C HC1 HC2.
  have: C \in channels P1.
  apply (fsubsetP Hsub); elim (andP HC1); done.
  move => Cin1.
  move/all_fsetP: (H _ Cin1).
  move/andP: Hc1 => [Hc1 _].
  move/(_ _ Hc1).
  move/fdisjointP.
  move/(_ _ HC2).
  rewrite Hc2; done.
Qed.

Lemma compat_disjoint_c_hiddens1 {A} (P2 P1 : @PIOA A) (H : compatible P1 P2) cs :
  (cs `<=` channels P2)%fset -> [disjoint (cover cs) & (hiddens P1)]%fset.
  move=> Hsub.
  apply/fdisjointP => x Hx1.
  apply/bigfcupP; elim => y Hc1 Hc2.

  move/and4P: H; elim => [_ _ /all_fsetP H _].

  move/bigfcupP: Hx1; elim => C HC1 HC2.
  have: C \in channels P2.
  apply (fsubsetP Hsub); elim (andP HC1); done.
  move => Cin2.
  move/andP: Hc1 => [Hc1 _].
  move/all_fsetP: (H _ Hc1).
  move/(_ _ Cin2).
  move/fdisjointP.
  move/(_ _ Hc2).
  rewrite HC2; done.
Qed.

Local Open Scope fset.

Lemma bool_iffP (b1 b2 : bool) : reflect (b1 <-> b2) (b1 == b2).
  apply/(iffP idP).
  move/eqP => ->; rewrite //=.
  move => H.
  destruct b1.
  apply/eqP; symmetry; apply H; rewrite //=.
  destruct b2.
  have: false by apply H; done.
  done.
  done.
Qed.

  Lemma coverU {X : choiceType} (F G : {fset {fset X}}) :
    cover (F `|` G) = cover F `|` cover G.
    rewrite /cover .
    apply/fsetP => x.
    apply/eqP/bool_iffP; split.
    move/bigfcupP; elim => x0; move/andP; elim; move/fsetUP; elim.
    intros; apply/fsetUP; left; apply/bigfcupP; exists x0; rewrite ?(H, H0) //=.
    intros; apply/fsetUP; right; apply/bigfcupP; exists x0; rewrite ?(H, H0) //=.
    move/fsetUP; elim.
    move/bigfcupP; elim => x0; move/andP; elim; intros; apply/bigfcupP; exists x0.
    apply/andP; split; rewrite //=.
    apply/fsetUP; left; apply H.
    done.
    move/bigfcupP; elim => x0; move/andP; elim; intros; apply/bigfcupP; exists x0.
    apply/andP; split; rewrite //=.
    apply/fsetUP; right; apply H.
    done.
  Qed.

    
    Check fsetDP.

Lemma notin_fsetU : forall {T : choiceType} {s1 s2 : {fset T}} {x},
                          (x \notin s1 `|` s2) = ((x \notin s1) && (x \notin s2)).
by intros; rewrite in_fsetU negb_or; done.
Qed.

Lemma notincover : forall {T : choiceType} (x : T) (s : {fset {fset T}}), 
                            (x \notin (cover s)) <-> 
                            ((forall t, (t \in s) -> (x \notin t))).
  intros; split; intros.
  apply/contraT.
  rewrite negbK; intros.
  move/bigfcupP: H.
  elim.
  exists t.
  rewrite H0 //=.
  rewrite H1 //=.

  apply/bigfcupP.
  elim.
  intros.
  apply/negP.
  instantiate (1 := x \in x0); rewrite //=.
  apply H.
  move/andP: H0; elim; done.
  done.
Qed.

Lemma disjoint_coverD_l {T : choiceType} (f1 f2 : {fset {fset T}}) (d : {fset T}) :
  [disjoint (cover f1) & d]%fset -> [disjoint (cover (f1 `\` f2)) & d]%fset.
  move/fdisjointP => H; apply/fdisjointP => x Hx.
  apply H.
  move/bigfcupP: Hx; elim => t Ht1 Ht2.
  apply/bigfcupP; exists t; rewrite //=.
  apply/andP; split; rewrite //=; rewrite in_fsetD in Ht1; move/andP: Ht1 => [/andP [ht1 ht2] _]; done.
Qed.

Section CompPIOA.
  Context {A : choiceType}.
  Context (P1 P2 : @PIOA A).
  Context (Hcompat : compatible P1 P2).

    Print prePIOA.
    Definition compPre : @prePIOA A := Build_prePIOA A ([fastEnumType of pQ P1 * pQ P2])%type (start P1, start P2) (cO P1 `|` cO P2)%fset ((cI P1 `|` cI P2) `\` (cO P1 `|` cO P2))%fset (cH P1 `|` cH P2)%fset
  (fun s a =>
     match tr P1 s.1 a, tr P2 s.2 a with
       | Some mu1, Some mu2 => Some (x <- mu1; y <- mu2; ret (x,y))
       | None, Some mu2 => if a \notin actions P1 then Some (y <- mu2; ret (s.1, y)) else None
       | Some mu1, None => if a \notin actions P2 then Some (x <- mu1; ret (x, s.2)) else None
       | None, None => None
                         end).

    Definition compPre_axiom : PIOA_axiom compPre. (* true but very tedious *)
      apply/and4P; split.
      apply/and4P; split.
      rewrite /inputs /outputs //=.
      admit.
      rewrite /inputs /hiddens //=; apply disjoint_coverD_l; rewrite !coverU fdisjointUX !fdisjointXU.
      apply/and3P; split.
      apply/andP; split.
      move/and4P: (PIOAAxiom P1) => [e _ _ _]; move/and4P: e; elim; done.
      apply (compat_disjoint_c_hiddens2 P1); rewrite //=.
      apply fsubsetU; apply/orP; left; apply fsubsetU; apply/orP; left; done.
      apply (compat_disjoint_c_hiddens1 P2); rewrite //=.
      apply fsubsetU; apply/orP; left; apply fsubsetU; apply/orP; left; done.
      move/and4P: (PIOAAxiom P2) => [e _ _ _]; move/and4P: e; elim; done.

      rewrite /outputs /hiddens //=; rewrite !coverU fdisjointUX !fdisjointXU.
      apply/and3P; split.
      apply/andP; split.
      move/and4P: (PIOAAxiom P1) => [e _ _ _]; move/and4P: e; elim; done.
      apply (compat_disjoint_c_hiddens2 P1); rewrite //=.
      apply fsubsetU; apply/orP; left; apply fsubsetU; apply/orP; right; done.
      apply (compat_disjoint_c_hiddens1 P2); rewrite //=.
      apply fsubsetU; apply/orP; left; apply fsubsetU; apply/orP; right; done.
      move/and4P: (PIOAAxiom P2) => [e _ _ _]; move/and4P: e; elim; done.

      admit.

      apply/all_fsetP => a Ha; apply/forallP => s.
      rewrite //=.
      admit.
      admit.
      admit.
    Admitted.
    Definition CompPIOA := Build_PIOA A compPre compPre_axiom.
End CompPIOA.








