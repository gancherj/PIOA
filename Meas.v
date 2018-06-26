Add LoadPath "~/fcf/src".
Add LoadPath ".".
Require Import FCF.Rat.
Require Import FCF.Fold.
Require Import CpdtTactics.
Require Import FcfLems.
Require Import Ring.
Require Import List.
Require Import Coq.Classes.Equivalence.
Require Import Relation_Definitions.
Require Import Program.
Require Import FCF.StdNat.
Require Import Eqdep_dec.
Open Scope rat_scope.



Lemma sr_rat : @semi_ring_theory Rat 0 1 ratAdd ratMult eqRat.
  econstructor.
  intros; rewrite <- ratAdd_0_l; auto.
  crush.
  intros; rewrite ratAdd_comm; crush.
  intros; rewrite ratAdd_assoc; crush.
  intros; rewrite ratMult_1_l; crush.
  intros; rewrite ratMult_0_l; crush.
  intros; rewrite ratMult_comm; crush.
  intros; rewrite ratMult_assoc; crush.
  intros; rewrite ratMult_comm; rewrite ratMult_distrib; rewrite ratMult_comm; apply ratAdd_eqRat_compat; [crush | apply ratMult_comm; crush].
  Defined.


Add Ring ratring : sr_rat.

(* Linear combinations of elements of A *)
Definition Meas (A : Type) : Type := list (Rat * A).

Definition ratDisp (r : Rat) : nat * nat :=
  match r with
  | RatIntro n1 p =>
    match p with
    | exist _ n2 _ => (n1, n2)
    end
  end.

Definition MeasDisp {A} (d : Meas A) : list ((nat * nat) * A) :=
  map (fun p => (ratDisp (fst p), snd p)) d.

Section MeasOps.
  Context {A : Type}.
  Definition measMass (d : Meas A) := sumList (map fst d) (fun x => x).
  (* A measure is a distribution when it has total mass 1 and all elements have positive mass *)
  (* TODO: I can now remove the = 0 condition. *)
  Definition isDist (d : Meas A) :=
    (measMass d == 1).
  Definition measRed (d : Meas A) :=
    filter (fun p => negb (beqRat (fst p) 0)) d.
  Definition measSupport (d : Meas A) := map snd (measRed d).
  Definition integ (d : Meas A) (f : A -> Rat) :=
    sumList (map (fun p => (fst p) * (f (snd p))) d) (fun x => x).

  Definition measEquiv (d1 d2 : Meas A) := forall f, integ d1 f == integ d2 f.

End MeasOps.

Section MeasMonad.
  Context {A B : Type}.

  Definition measRet (a : A) : Meas A := (1, a) :: nil.
  Lemma isDist_ret : forall a, isDist (measRet a).
    intros.
    unfold isDist, measRet.
    unfold measMass.
    crush.
    unfold sumList; crush.
    ring.
  Qed.

  Definition measScale (r : Rat) (d : Meas B) :=
    map (fun p => (r * (fst p), snd p)) d.

  Definition measSum (ds : list (Meas B)) := concat ds.
  
  Definition measJoin (d : Meas (Meas B)) : Meas B :=
    measSum (map (fun p => measScale (fst p) (snd p)) d).

  Definition measBind (d : Meas A) (f : A -> Meas B) : Meas B :=
    measJoin (map (fun p => (fst p, f (snd p))) d).
   


End MeasMonad.

Lemma measJoin_cons {A : Type} (d : Meas (Meas A)) a :
  measJoin (a :: d) = (measScale (fst a) (snd a)) ++ (measJoin d).
  unfold measJoin.
  simpl.
  crush.
Qed.

Lemma integ_nil {A : Type} (f : A -> Rat) : integ [] f == 0.
  unfold integ;
    rewrite sumList_nil;
    crush.
Qed.

Lemma integ_cons {A : Type} (d1 : Meas A) a f : integ (a :: d1) f == (fst a) * f (snd a) + integ d1 f.
  unfold integ.
  simpl.
  rewrite sumList_cons.
  crush.
Qed.

Lemma integ_app {A : Type} (d1 d2 : Meas A) f : integ (d1 ++ d2) f == integ d1 f + integ d2 f.
  unfold integ.
  rewrite map_app; simpl.
  rewrite sumList_app.
  crush.
Qed.

Lemma integ_measScale {A : Type} (d1 : Meas A) r f :
  integ (measScale r d1) f == r * (integ d1 f).
  unfold integ, measScale.
  rewrite map_map.
  simpl.
  induction d1.
  crush.
  rewrite sumList_nil.
  ring.
  simpl.
  repeat rewrite sumList_cons.
  rewrite IHd1.
  crush.
  ring.
Qed.

Lemma integ_measJoin {A : Type} (d : Meas (Meas A)) (f : A -> Rat) :
  integ (measJoin d) f == integ d (fun d' => integ d' f).
  induction d.
  unfold measJoin, integ; crush.
  rewrite measJoin_cons.
  rewrite integ_app.
  rewrite integ_cons.
  rewrite IHd.
  rewrite integ_measScale.
  ring.
Qed.

Lemma integ_measBind {A B : Type} (d : Meas A) (df : A -> Meas B) f :
  integ (measBind d df) f == integ d (fun x => integ (df x) f).
  unfold measBind.
  rewrite integ_measJoin.
  induction d.
  crush.
  unfold integ; crush.
  rewrite integ_cons.
  rewrite <- IHd.
  simpl.
  rewrite integ_cons.
  simpl; ring.
Qed.

Lemma integ_cong_l {A : Type} (d : Meas A) (f1 f2 : A -> Rat) :
  (forall x, In x (measSupport d) -> f1 x == f2 x) ->
  integ d f1 == integ d f2.
  unfold integ.
  crush.
  induction d; crush.
  destruct (eq_Rat_dec (fst a) 0).

  repeat rewrite sumList_cons.
  rewrite e.
  rewrite IHd.
  ring.
  intros.
  assert (In x (measSupport (a :: d))).
  unfold measSupport in *.
  simpl.
  rewrite e.
  crush.
  apply H; crush.
  repeat rewrite sumList_cons.
  rewrite IHd.
  rewrite H.
  ring.
  unfold measSupport.
  simpl.
  apply (Bool.not_true_is_false _) in n.
  rewrite n.
  crush.
  intros.
  apply H.
  unfold measSupport.
  apply (Bool.not_true_is_false _) in n.
  simpl.
  rewrite n.
  crush.
Qed.


Notation "'ret' x" := (@measRet  _ x) (at level 75).
Notation "x <- c1 ; c2" := (@measBind _ _ c1 (fun x => c2))
   (right associativity, at level 81, c1 at next level).                       



Notation "x ~~ y" := (@measEquiv _ x y) (at level 60).

Lemma integ_cong_r {A : Type} (d1 d2 : Meas A) (f : A -> Rat) :
  d1 ~~ d2 -> integ d1 f == integ d2 f.
  crush.
Qed.

Require Import Setoid.

Lemma equiv_symm {A : Type} : forall (d1 d2 : Meas A),
    d1 ~~ d2 -> d2 ~~ d1.
  intros; unfold measEquiv in *; intros; crush.
Qed.

Lemma equiv_trans {A : Type} : forall (d1 d2 d3 : Meas A),
    d1 ~~ d2 -> d2 ~~ d3 -> d1 ~~ d3.
  intros; unfold measEquiv in *; intros; crush.
Qed.

Lemma measEquiv_refl {A : Type} : forall (d : Meas A), d ~~ d.
  intros; unfold measEquiv; intros; crush.
Qed.

Add Parametric Relation (A : Type) : (Meas A) (@measEquiv A)
   symmetry proved by equiv_symm
   transitivity proved by equiv_trans
   as meas_eq
.

(* Lemmas about monadic operations and ~~ *)

  Lemma bindAssoc {A B C : Type} : forall (c1 : Meas A) (c2 : A -> Meas B) (c3 : B -> Meas C),
    (x <- (y <- c1; c2 y); c3 x) ~~ (y <- c1; x <- c2 y; c3 x).
    intros.
    unfold measEquiv; intros.
    repeat rewrite integ_measBind.
    apply integ_cong_l; intros.
    repeat rewrite integ_measBind.
    apply integ_cong_l; intros.
    crush.
  Qed.

  Lemma bindRet {A B : Type} (x : A) (c : A -> Meas B) :
    (z <- (ret x); c z) ~~ c x.
    intros; unfold measEquiv; intros.
    repeat rewrite integ_measBind.
    unfold measRet.
    rewrite integ_cons.
    simpl.
    rewrite integ_nil.
    ring.
  Qed.

  Lemma bindRet_r {A : Type} (c : Meas A) :
    (x <- c; ret x) ~~ c.
    unfold measEquiv; intros.
    rewrite integ_measBind.
    apply integ_cong_l; intros.
    unfold measRet.
    rewrite integ_cons; rewrite integ_nil; crush.
    ring.
  Qed.

Ltac in_sumList_l := eapply eqRat_trans; [ apply sumList_body_eq; intros; simpl | idtac] .


Lemma measBind_cong_l {A B : Type} {d d' : Meas A} {c : A -> Meas B} :
  d ~~ d' ->
  measBind d c ~~ measBind d' c.
  intros.
  unfold measEquiv; intros.
  repeat rewrite integ_measBind.
  apply integ_cong_r.
  crush.
Qed.

Lemma measBind_cong_r {A B : Type} {d : Meas A} {c1 c2 : A -> Meas B} :
  (forall x, In x (measSupport d) -> c1 x ~~ c2 x) ->
  measBind d c1 ~~ measBind d c2.
  intros.
  unfold measEquiv; intros; repeat rewrite integ_measBind.
  apply integ_cong_l.
  crush.
  apply H.
  crush.
Qed.

Lemma measBind_app {A B : Type} (d1 d2 : Meas A) (c : A -> Meas B) :
  (p <- (d1 ++ d2); c p) ~~
                         ((p <- d1; c p) ++ (p <- d2; c p)).
  unfold measBind.
  unfold measJoin.
  rewrite map_app.
  rewrite map_app.
  unfold measSum.
  rewrite concat_app.
  unfold measEquiv; intros; crush.
Qed.


Lemma measEquiv_cons_cong {A : Type} {a b : (Rat * A)} (d1 d2 : Meas A) :
  (fst a == fst b /\ snd a = snd b) ->
  d1 ~~ d2 ->
  (a :: d1) ~~ (b :: d2).
  unfold measEquiv; unfold integ; intros.
  simpl.
  repeat rewrite Fold.sumList_cons.
  rewrite H0.
  destruct H.
  rewrite H.
  rewrite H1.
  ring.
Qed.

Lemma measEquiv_app_cong {A : Type} {d1 d2 d3 d4 : Meas A} :
  d1 ~~ d2 ->
  d3 ~~ d4 ->
  (d1 ++ d3) ~~ (d2 ++ d4).
  unfold measEquiv; unfold integ; intros.
  repeat rewrite map_app.
  repeat rewrite sumList_app.
  rewrite H.
  rewrite H0.
  ring.
Qed.

Lemma measBind_cons {A B : Type} (d1 : Meas A) (c : A -> Meas B) a :
  (p <- a :: d1; c p) ~~ (measScale (fst a) (c (snd a)) ++ (p <- d1; c p)).
  unfold measEquiv; intros.
  repeat rewrite integ_measBind.
  repeat rewrite integ_cons.
  repeat rewrite integ_app.
  repeat rewrite integ_measScale.
  repeat rewrite integ_measBind.
  crush.
Qed.

Lemma measScale_bind_l {A B : Type} (d : Meas A) (f : A -> Meas B) (r : Rat) :
  measScale r (p <- d; f p) ~~
            (p <- (measScale r d); f p).
  unfold measEquiv; intros.
  rewrite integ_measScale.
  repeat rewrite integ_measBind.
  rewrite integ_measScale.
  ring.
Qed.

Lemma measScale_cong {A : Type} (d1 d2 : Meas A) (r : Rat) :
  d1 ~~ d2 ->
  (measScale r d1) ~~ (measScale r d2).
  intros; unfold measEquiv; intros.
  repeat rewrite integ_measScale.
  rewrite (H f).
  crush.
Qed.


Lemma measEquiv_zero_cons {A : Type} (d : Meas A) (a : Rat * A) :
  fst a == 0 -> d ~~ (a :: d).
  intros.
  unfold measEquiv, integ; intros.
  rewrite map_cons.
  rewrite sumList_cons.
  rewrite H.
  ring.
Qed.

Lemma filter_app {A} (l1 l2 : list A) f : filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  induction l1.
  crush.
  simpl.
  rewrite IHl1.
  destruct (f a); crush.
Qed.
  
Lemma measSupport_app {A : Type} (d1 d2 : Meas A) :
  measSupport (d1 ++ d2) = measSupport d1 ++ measSupport d2.
  unfold measSupport.
  unfold measRed.
  rewrite filter_app.
  rewrite map_app.
  crush.
Qed.

Lemma measSupport_cons {A : Type} (d : Meas A) (a : Rat * A) :
  measSupport (a :: d) = (if beqRat (fst a) 0 then measSupport d else (snd a) :: measSupport d).
  unfold measSupport.
  crush.
  destruct (beqRat a0 0); crush.
Qed.

Lemma measSupport_measScale {A : Type} (d : Meas A) (r : Rat) :
  ~ (r == 0) -> measSupport d = measSupport (measScale r d).
  intros.
  induction d.
  crush.
  simpl.
  repeat rewrite measSupport_cons.
  simpl.
  remember (beqRat (fst a) 0).
  destruct b.
  assert (fst a == 0). unfold eqRat; crush.
  assert (r * fst a == 0).
  rewrite H0.
  ring.
  rewrite H1.
  crush.

  assert (~ (r * fst a == 0)).
  apply ratMult_nz.
  crush.
  remember (beqRat (r * fst a) 0) as b; destruct b.
  crush.
  crush.
Qed.

Lemma measIndicator_in_support {A : Type} (H : forall x y : A, {x = y} + {x <> y}) (d : Meas A) : forall p, 
    (~ (integ d (fun x => if H x p then 1 else 0) == 0)) <->
    In p (measSupport d).
  split.
  intros.
  induction d.
  unfold integ in H0; rewrite sumList_nil in H0.
  crush.
  rewrite integ_cons in H0.
  apply ratAdd_nz in H0.
  destruct H0.
  apply ratMult_nz in H0.
  destruct H0.
  rewrite measSupport_cons.
  rewrite (Bool.not_true_is_false _ H0).
  destruct (H (snd a) p).
  crush.
  crush.
  rewrite measSupport_cons.
  destruct (beqRat (fst a) 0).
  apply IHd; crush.
  right; apply IHd; crush.

  intros.
  induction d.
  crush.
  rewrite integ_cons.
  rewrite measSupport_cons in H0.
  destruct (eq_Rat_dec (fst a) 0).
  apply ratAdd_nz.
  right.
  apply IHd.
  rewrite e in H0.
  crush.

  rewrite (Bool.not_true_is_false _ n) in H0.
  destruct H0.
  apply ratAdd_nz.

  left.
  subst.
  destruct (H (snd a) (snd a)).
  apply ratMult_nz; crush.
  crush.
  apply ratAdd_nz; right; apply IHd; crush.
Qed.
  
                           
Lemma measSupport_measEquiv {A : Type} (H : forall x y : A, {x = y} + {x <> y}) (d1 d2 : Meas A) :
  d1 ~~ d2 -> forall p, In p (measSupport d1) -> In p (measSupport d2). 
  intros.
  apply (measIndicator_in_support H) in H1.
  apply (measIndicator_in_support H).
  intro.
  rewrite (H0 (fun x => if H x p then 1 else 0)) in H1.
  crush.
Qed.  

(*
Lemma sumList_zip {A : Type} (l l' : list A) (f f' : A -> Rat) :
  length l = length l' ->
  (forall p, In p (zip l l') -> f (fst p) == f' (snd p)) ->
  sumList l f == sumList l' f'.
  revert l'.
  induction l.
  induction l'.
  crush.
  unfold sumList; crush.
  crush.
  intros.
  induction l'.
  crush.
  assert (sumList l f == sumList l' f').
  apply IHl.
  crush.
  intros.
  simpl in H0.
  apply H0; crush.
  repeat rewrite sumList_cons.
  rewrite H1.
  pose proof (H0 _ (or_introl (eq_refl (a, a0)))); simpl in *.
  rewrite H2.
  crush.
Qed.
*)

Lemma measEquiv_app_symm {A : Type} (d1 d2 : Meas A) :
  (d1 ++ d2) ~~ (d2 ++ d1).
  unfold measEquiv, integ; intros.
  repeat rewrite map_app.
  repeat rewrite sumList_app.
  ring.
Qed.

Lemma measEquiv_rev {A : Type} (d : Meas A) :
  d ~~ (rev d).
  induction d.
  unfold measEquiv; crush.
  simpl.
  assert (a :: d = [a] ++ d).
  crush.
  rewrite H.
  rewrite measEquiv_app_symm.
  apply measEquiv_app_cong.
  crush.
  unfold measEquiv; crush.
Qed.

(*
Lemma measBind_zip {A B : Type} {d d' : Meas A} {c c' : A -> Meas B} :
  length d = length d' ->
  (forall p, In p (zip d d') -> fst (fst p) == fst (snd p) /\ c (snd (fst p)) ~~ c' (snd (snd p))) ->
  measBind d c ~~ measBind d' c'.

  intros.
  unfold measBind, measJoin, measEquiv, measSum, integ; intros.
  repeat rewrite sumList_concat.
  repeat rewrite sumList_map.
  eapply sumList_zip.
  crush.
  intros.
  simpl.
  destruct (H0 _ H1).
  unfold measScale.
  repeat rewrite sumList_map.
  simpl.
  etransitivity.
  apply sumList_body_eq; intros; apply ratMult_assoc.
  symmetry; etransitivity.
  apply sumList_body_eq; intros; apply ratMult_assoc.
  repeat rewrite sumList_factor_constant_l.
  apply ratMult_eqRat_compat.
  crush.
  symmetry; apply (H3 f).
Qed.
*)


(*
Global Instance nz_length_app {A} (l1 l2 : list A) {H1 : nz (length l1)} {H2 : nz (length l2)} : nz (length (l1 ++ l2)).
destruct H1.
destruct H2.
constructor.
rewrite app_length.
crush.
Defined.

Global Instance nz_allnatslt_length (n : nat) {H1 : nz n} : nz (length (allNatsLt n)).
destruct n.
destruct H1; crush.
simpl.
rewrite app_length.
crush.
constructor.
crush.
Defined.
*)

(* uniformity *)


(* Proof irrelevent inverses *)

Definition natpos (n : nat) :=
  match n with | 0 => false | _ => true end = true.


Global Instance natpos_nz (n : nat) {H : natpos n} : nz n.
destruct n; crush.
Defined.

Definition natInverse (n : nat) {H : natpos n} : Rat.
  apply RatIntro.
  apply 1%nat.
  eapply exist.
  apply natpos_nz.
  apply H.
Defined.

Notation "1 // n" := (match n with | 0 => 0 | S m => @natInverse (S m) eq_refl end) (at level 60).  

Lemma natpos_irrel {n : nat} (H1 H2 : natpos n) : H1 = H2.
  destruct n; crush.
  unfold natpos in *.
  apply eq_proofs_unicity.
  decide equality.
Qed.

Definition unif {A : Type} (xs : list A) : Meas A :=
  match (length xs) with
  | 0 => nil
  | S n => 
    map (fun x => (1 // (S n), x)) xs
        end.

Definition unifNats (n : nat) : Meas (nat) := unif (allNatsLt n).


Lemma unif_cons {A : Type} (l1 : list A) (a : A) :
  unif (a :: l1) = ((1 // S (length l1), a) :: (map (fun p => (1 // (S (length l1)), snd p)) (unif l1))).
  unfold unif; simpl.
  destruct l1.
  crush.
  simpl.
  rewrite map_map.
  simpl.
  crush.
Qed.


Lemma unif_app {A : Type} (l1 l2 : list A) :
  unif (l1 ++ l2) = map (fun p => (1 // length (l1 ++ l2), snd p)) (unif l1 ++ unif l2).
  unfold unif.
  destruct l1; destruct l2; simpl.
  crush.
  rewrite map_map; crush.
  repeat rewrite app_nil_r; simpl.
  rewrite map_map; simpl.
  crush.
  repeat rewrite map_app.
  repeat rewrite map_map.
  simpl.
  repeat rewrite map_map.
  simpl.
  crush.
Qed.

Lemma unifNats_in (n : nat) : forall p,
    In p (measSupport (unifNats n)) -> p < n.
  induction n.
  crush.
  crush.
  unfold unifNats in H.
  simpl in H.
  rewrite unif_app in H.
  unfold measSupport in H.
  unfold measRed in H.
  rewrite map_app in H; crush.
  rewrite filter_app in H.
  simpl in H.
  rewrite map_app in H.
  apply in_app_iff in H; crush.
  assert (In p (measSupport (unifNats n))).
  apply in_map_iff in H0; crush.
  apply filter_In in H1; crush.
  apply in_map_iff in H; crush.
  apply in_map_iff; exists x0.
  crush.
  unfold measRed.
  apply filter_In; crush.
  clear H0.
  clear IHn.
  destruct n.
  crush.
  simpl in H2.
  rewrite unif_app in H2.
  rewrite map_app in H2; simpl in *.
  destruct x0; apply in_app_iff in H2; crush.
  apply in_map_iff in H; crush.
  unfold natInverse.
  rewrite app_length.
  simpl.
  remember (length (allNatsLt n) + 1)%nat.
  destruct n0.
  destruct (length (allNatsLt n)); crush.
  crush.
  unfold natInverse; rewrite app_length.
  simpl.
  remember (length (allNatsLt n0) + 1)%nat.
  destruct n.
  destruct (length (allNatsLt n0)); crush.
  destruct (length (allNatsLt n0) + 1)%nat; crush.
  apply Nat.lt_lt_succ_r.
  crush.
  apply in_map_iff in H0; crush.
  destruct x; simpl.
  remember (negb (beqRat (1 // length (allNatsLt n ++ [n])) 0)).
  destruct b.
  simpl in H1.
  crush.
  crush.
Qed.

Lemma in_concat_iff {A} : forall (x : A) (ls : list (list A)),
      In x (concat ls) <-> exists l, In l ls /\ In x l.
    intros.
    split.
    induction ls.
    intros.
    inversion H.
    intros.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    exists a.
    crush.
    destruct (IHls H).
    exists x0.
    crush.

    intros.
    destruct H.
    induction ls.
    crush.
    simpl.
    destruct H.
    apply in_app_iff.
    crush.
  Qed.

Lemma measBind_in {A B} (d : Meas A) (d' : A -> Meas B) :
  forall y, In y (measSupport (measBind d d')) <-> exists x,
      In x (measSupport d) /\ In y (measSupport (d' x)).
  split; intros.
  unfold measSupport, measBind, measRed, measJoin in H.
  rewrite map_map in H; simpl in H.
  unfold measSum in H.
  apply in_map_iff in H; crush.
  apply filter_In in H1; crush.

  apply in_concat_iff in H; crush.
  apply in_map_iff in H1; crush.
  unfold measScale in H2.
  apply in_map_iff in H2; crush.

  destruct (eq_Rat_dec (fst x1) 0).
  assert ((fst x1) * (fst x0) == 0).
  rewrite e; ring.
  rewrite H in H0.
  crush.
  destruct (eq_Rat_dec (fst x0) 0).
  assert (fst x1 * fst x0 == 0). rewrite e; ring.
  rewrite H in H0; crush.


  exists (snd x1).
  split.
  unfold measSupport.
  unfold measRed.
  apply in_map_iff.
  exists x1.
  crush.
  apply filter_In.
  crush.
  unfold measSupport.
  unfold measRed.
  apply in_map_iff; exists x0.
  crush.
  apply filter_In.
  crush.

  destruct H.
  unfold measBind, measSupport.
  crush.
  unfold measSupport in *.
  apply in_map_iff in H0; crush.
  apply in_map_iff in H1; crush.
  unfold measRed in *.
  apply filter_In in H2; crush.
  apply filter_In in H1; crush.
  apply in_map_iff.

  exists (fst x0 * fst x, snd x).
  crush.
  apply filter_In.
  crush.
  unfold measJoin.
  unfold measSum.
  rewrite map_map.
  unfold measScale.
  simpl.
  apply in_concat_iff.
  exists (measScale (fst x0) (d' (snd x0))).
  crush.
  apply in_map_iff.
  exists x0.
  crush.
  apply in_map_iff.
  exists x.
  crush.

  rewrite Bool.negb_true_iff in *.
  assert (forall n, n = false <-> n <> true).
  destruct n; crush.
  apply H1.
  apply ratMult_nz.
  crush.
Qed.

  Ltac dsimp := repeat (simpl; 
    match goal with
    | [ |- context[_ <- ret _; _] ] => rewrite bindRet
    | [ |- context[_ <- (_ <- _; _); _] ] => rewrite bindAssoc
    | [ |- context[_ <- _; ret _] ] => rewrite bindRet_r
    | [ |- ?H ~~ ?H ] => apply measEquiv_refl
                                            end; simpl).

  Ltac dsimp_in_l := etransitivity; eapply measBind_cong_r; intros; dsimp; apply measEquiv_refl.
  Ltac dsimp_in_r := symmetry; etransitivity; eapply measBind_cong_r; intros; dsimp; apply measEquiv_refl; symmetry.

