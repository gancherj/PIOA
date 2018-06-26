Add LoadPath "~/fcf/src".
Require Import Meas.
Require Import Program.
Require Import Expansion.
Require Import FCF.Rat.
Require Import Ring.
Require Import List.
Require Import CpdtTactics.
Require Import Ott.ott_list.
From mathcomp Require Import ssreflect ssrfun ssrbool finset.
From extructures Require Import ord fset.

Record prePIOA {A : Type} :=
  mkPIOA {
      pQ : Set;
      start : pQ;
      tr : pQ -> A -> option (Meas pQ)
                           }.

Definition actionDeterm {S : ordType} (P : @prePIOA S) (T : {fset S}) :=
  forall s x y, x \in T -> tr P s x <> None -> y \in T -> tr P s y <> None -> x = y.

Record TaskStructure {T} {S : ordType} (P : @prePIOA S) {O H : {fset S} } :=
  {
    actionsOf :> T -> {fset S};
    _ : forall t, fsubset (actionsOf t) O \/ fsubset (actionsOf t) H;
    _ : forall t, actionDeterm P (actionsOf t);
    _ : forall t1 t2, t1 <> t2 -> fdisjoint (actionsOf t1) (actionsOf t2);
    transProj : T -> pQ P -> option S;
    _ : forall s t x, (transProj t s = Some x) <-> (tr P s x <> None);
    _ : forall s t x, transProj t s = Some x -> x \in (actionsOf t)
                                                     }.

Record PIOA {ActSpace : ordType} :=
{
  Tasks : Type;
  I : {fset ActSpace};
  O : {fset ActSpace};
  H : {fset ActSpace};
  pP :> @prePIOA ActSpace;
  TS :> @TaskStructure Tasks ActSpace pP O H;
  _ : fdisjoint I O;
  _ : fdisjoint I H;
  _ : fdisjoint O H;
  inputEnabled : forall s x, x \in I -> tr pP s x <> None;
  actSetValid : forall s x, tr pP s x <> None -> x \in (I :|: (O :|: H))%fset
  }.

Definition Trace {ActSpace} (P : @PIOA ActSpace) :=
  ((pQ P) * (list ActSpace))%type.

Definition startTr {A} (P : @PIOA A) : Meas (Trace P) :=
  ret (start P, nil).

Definition appTask {ActSpace : ordType} (P : @PIOA ActSpace) (T : Tasks P) (mu : Meas (Trace P)) : Meas (Trace P) := 
  t <- mu;
  let (s, actions) := t in
  match (transProj P (TS P) T s) with
  | Some a =>
    match (tr P s a) with
    | Some mu =>
      s' <- mu;
      if (a \in ((I P) :|: (O P))%fset) then ret (s', a :: actions) else ret (s', actions)
    | None => ret t
    end
  | _ => ret t
           end.

Lemma appTask_distrib {A} (P : @PIOA A) (T : Tasks P) :
  joinDistrib (appTask P T).
  unfold joinDistrib, appTask; intros; dsimp; apply measEquiv_refl.
Qed.

Lemma appTask_cong {A} (P : @PIOA A) (T : Tasks P) :
  measCong (appTask P T).
  unfold measCong, appTask; intros; dsimp; rewrite (measBind_cong_l H0); apply measEquiv_refl.
Qed.


Definition runPIOA {A} (P : @PIOA A) (ts : list (Tasks P)) (d : Meas (Trace P)) : Meas (Trace P) :=
  fold_right (fun t acc => appTask P t acc) d ts.


Lemma runPIOA_cons {A} (P : @PIOA A) (t : Tasks P) (ts : list (Tasks P)) d :
  runPIOA P (t :: ts) d = appTask P t (runPIOA P ts d).
  unfold runPIOA.
  simpl.
  auto.
Qed.

Lemma runPIOA_app {A} (P : @PIOA A) (ts ts' : list (Tasks P)) d :
  runPIOA P (ts ++ ts') d = runPIOA P ts (runPIOA P ts' d).
  unfold runPIOA.
  rewrite fold_right_app.
  auto.
Qed.

Lemma runPIOA_cong {A} (P : @PIOA A) ts :
  measCong (runPIOA P  ts).
  unfold measCong, runPIOA; intros.
  induction ts.
  simpl.
  crush.
  simpl.
  rewrite (appTask_cong _ _ _ _ IHts).
  apply measEquiv_refl.
Qed.
      
  
Lemma runPIOA_distrib {A} {P : @PIOA A} ts :
  joinDistrib (runPIOA P ts).
  induction ts.
  unfold joinDistrib, runPIOA.
  crush.
  apply measEquiv_refl.
  unfold joinDistrib in *.
  intros.
  repeat rewrite runPIOA_cons.
  etransitivity.
  apply appTask_cong.
  rewrite IHts.
  apply measEquiv_refl.
  simpl.
  symmetry in IHts.
  unfold appTask.
  dsimp.
  apply measEquiv_refl.
Qed.

Definition traceOf {Q act} (D : Meas (Q * list act)) :=
  fmap D snd.

Definition inputClosed {A} (P : @PIOA A) :=
  (I P) = (fset nil).

Definition inputEquiv {A} (P1 P2 : @PIOA A) :=
  (I P1) = (I P2).

Definition refinement {A} (P1 P2 : @PIOA A)  `{inputClosed P1} `{inputClosed P2} :=
  forall ts, exists ts',
      traceOf (runPIOA P1 ts (startTr P1)) ~~ traceOf (runPIOA P2 ts' (startTr P2)).

Definition consistentWith {A} {P1 : @PIOA A} (ts : list (Tasks P1)) (d : Meas (Trace P1)) :=
  forall p, In p (measSupport d) -> In p (measSupport (runPIOA P1 ts (startTr P1))).

Record SimR {A} (P1 P2 : @PIOA A) 
       (R : Meas (Trace P1) -> Meas (Trace P2) -> Prop) :=
  {
    simStart : R (ret (start P1, nil)) (ret (start P2, nil));
    simTr : forall d1 d2, R d1 d2 -> traceOf d1 ~~ traceOf d2;
    simStep : forall ts T, exists ts', forall d1 d2, consistentWith ts d1 -> R d1 d2 ->
          (expansion R) (appTask P1 T d1) (runPIOA P2 ts' d2)}.


Lemma fmap_cong {A B} (d1 d2 : Meas A) (f : A -> B) :
  d1 ~~ d2 -> fmap d1 f ~~ fmap d2 f.
  intros. unfold fmap.
  rewrite (measBind_cong_l H0).
  apply measEquiv_refl.
Qed.
  

Lemma expansion_trace : forall {Q Q' act} (R : Meas (Q * list act) -> Meas (Q' * list act) -> Prop) d1 d2, (forall d1 d2, R d1 d2 -> traceOf d1 ~~ traceOf d2) -> expansion R d1 d2 -> traceOf d1 ~~ traceOf d2.
  intros.
  destruct H1.
  destruct H1.
  unfold traceOf.
  rewrite (fmap_cong _ _ _ leftEquiv).
  rewrite (fmap_cong _ _ _ rightEquiv).
  unfold fmap.
  dsimp.
  apply measBind_cong_r; intros.
  apply H0.
  apply RValid.
  crush.
Qed.


Lemma simSound {A} (P1 P2 : @PIOA A) R `{H: inputClosed P1} `{H2 : inputClosed P2} {Heqact : forall x y : A, {x = y} + {x <> y}} {HeqQ1 : forall x y : pQ P1, {x = y} + {x <> y}} :
  SimR P1 P2 R -> @refinement _ P1 P2 H H2.
  intro.
  destruct H0.
  unfold refinement.
  intros.
  cut (exists ts', (expansion R) (runPIOA P1 ts (startTr P1)) (runPIOA P2 ts' (startTr P2))).
  intro Hex; destruct Hex.
  exists x.
  apply (expansion_trace R).
  crush.
  crush.

  induction ts.
  exists nil.
  exists (ret (ret (start P1, []), ret (start P2, []))).
  constructor.
  simpl; rewrite bindRet; simpl; unfold startTr; unfold measEquiv; crush.
  simpl; rewrite bindRet; simpl; unfold startTr; unfold measEquiv; crush.
  intros.
  simpl in H0.
  destruct H0.
  2: { crush. }
  subst; simpl.
  apply simStart0.


  destruct IHts.
  destruct H0.
  destruct (simStep0 ts a).
  exists (x1 ++ x).
  rewrite runPIOA_app.
  rewrite runPIOA_cons.

  eapply joinDistrib_expansion_compat.
  apply appTask_cong.
  apply appTask_distrib.
  apply runPIOA_cong.
  apply runPIOA_distrib.
  apply H0.
  destruct H0.
  rewrite leftEquiv.
  unfold fmap;
  rewrite bindAssoc; apply measBind_cong_r; intros; rewrite bindRet; unfold measEquiv; crush.
  destruct H0.
  rewrite rightEquiv; unfold fmap;
  rewrite bindAssoc; apply measBind_cong_r; intros; rewrite bindRet; unfold measEquiv; crush.

  intros; apply H1.
  destruct H0.
  unfold consistentWith.
  intros.
  assert (In p0 (measSupport (p <- x0; fst p))).
  apply measBind_in.
  exists p.
  crush.

  eapply measSupport_measEquiv.

  decide equality.
  apply list_eq_dec; crush.
  symmetry; apply leftEquiv.
  crush.

  destruct H0.
  apply RValid.
  crush.
Qed.  
