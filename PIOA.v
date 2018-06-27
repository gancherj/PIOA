Add LoadPath "~/fcf/src".
Require Import Meas.
Require Import Program.
Require Import Expansion.
Require Import FCF.Rat.
Require Import Ring.
Require Import List.
Require Import CpdtTactics.
Require Import Ott.ott_list.
From mathcomp Require Import ssreflect ssrfun ssrbool finset eqtype fintype choice seq.

Record prePIOA {Act : finType} :=
  mkPrePIOA {
      pQ : finType;
      start : pQ;
      tr : pQ -> Act -> option (Meas pQ)
                           }.

Definition actionDeterm {Act : finType} (P : @prePIOA Act) (T : {set Act}) :=
  forall s x y, x \in T -> tr P s x <> None -> y \in T -> tr P s y <> None -> x = y.

Record TaskStructure {Act : finType} (P : @prePIOA Act) (O H : {set Act} ) (TO TH : {set {set Act}}) :=
  {
    _ : partition TO O;
    _ : partition TH H;
    _ : forall T, T \in (TO :|: TH) -> actionDeterm P T
                                                    }.

Record PIOA {Act : finType} :=
mkPIOA {
  pI : {set Act};
  pO : {set Act};
  pH : {set Act};
  pP :> @prePIOA Act;
  pTO : {set {set Act}};
  pTH : {set {set Act}};
  TS :> @TaskStructure Act pP pO pH pTO pTH;
  _ : trivIset ([set pI; pO; pH]);
  inputEnabled : forall s x, x \in pI -> tr pP s x <> None;
  actSetValid : forall s x, tr pP s x <> None -> x \in (pI :|: (pO :|: pH))
  }.

Definition Task {Act : finType} (P : @PIOA Act) := {set Act}.
Definition enabled {Act : finType} (P : @PIOA Act) (s : pQ P) :=
  fun a =>
    match (tr P s a) with | Some _ => true | None => false end.

Definition external {A} (P : @PIOA A) :=
  (pI P) :|: (pO P).
  
Definition Trace {ActSpace} (P : @PIOA ActSpace) :=
  ((pQ P) * (list ActSpace))%type.

Definition startTr {A} (P : @PIOA A) : Meas (Trace P) :=
  ret (start P, nil).

Definition appTask {Act : finType} (P : @PIOA Act) (T : Task P) (mu : Meas (Trace P)) : Meas (Trace P) := 
  t <- mu;
  let (s, actions) := t in
  match [pick x in T | enabled P s x] with
  | Some a =>
    match (tr P s a) with
    | Some mu =>
      s' <- mu;
      if (a \in (external P)) then ret (s', a :: actions) else ret (s', actions)
    | None => ret t
    end
  | _ => ret t
           end.

Lemma appTask_distrib {A} (P : @PIOA A) (T : Task P) :
  joinDistrib (appTask P T).
  unfold joinDistrib, appTask; intros; dsimp; apply measEquiv_refl.
Qed.

Lemma appTask_cong {A} (P : @PIOA A) (T : Task P) :
  measCong (appTask P T).
  unfold measCong, appTask; intros; dsimp; rewrite (measBind_cong_l H); apply measEquiv_refl.
Qed.

Definition runPIOA {A} (P : @PIOA A) (ts : seq (Task P)) (d : Meas (Trace P)) : Meas (Trace P) :=
  fold_right (fun t acc => appTask P t acc) d ts.


Lemma runPIOA_cons {A} (P : @PIOA A) (t : Task P) (ts : seq (Task P)) d :
  runPIOA P (t :: ts) d = appTask P t (runPIOA P ts d).
  unfold runPIOA.
  simpl.
  auto.
Qed.

Lemma runPIOA_app {A} (P : @PIOA A) (ts ts' : seq (Task P)) d :
  runPIOA P (ts ++ ts') d = runPIOA P ts (runPIOA P ts' d).
  unfold runPIOA; rewrite fold_right_app; auto.
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
  (pI P) = set0.

Definition inputEquiv {A} (P1 P2 : @PIOA A) :=
  (pI P1) = (pI P2).

Definition refinement {A} (P1 P2 : @PIOA A)  `{inputClosed P1} `{inputClosed P2} :=
  forall ts, exists ts',
      traceOf (runPIOA P1 ts (startTr P1)) ~~ traceOf (runPIOA P2 ts' (startTr P2)).

Definition consistentWith {A} {P1 : @PIOA A} (ts : seq (Task P1)) (d : Meas (Trace P1)) :=
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
  rewrite (measBind_cong_l H).
  apply measEquiv_refl.
Qed.
  

Lemma expansion_trace : forall {Q Q' act} (R : Meas (Q * list act) -> Meas (Q' * list act) -> Prop) d1 d2, (forall d1 d2, R d1 d2 -> traceOf d1 ~~ traceOf d2) -> expansion R d1 d2 -> traceOf d1 ~~ traceOf d2.
  intros.
  destruct H0.
  destruct H0.
  unfold traceOf.
  rewrite (fmap_cong _ _ _ leftEquiv).
  rewrite (fmap_cong _ _ _ rightEquiv).
  unfold fmap.
  dsimp.
  apply measBind_cong_r; intros.
  apply H.
  apply RValid.
  crush.
Qed.


Definition Comparable {A} (P1 P2 : @PIOA A) := (pI P1) = (pI P2) /\ (pO P1 = pO P2).

Lemma simSound {A} (P1 P2 : @PIOA A) R `{H: inputClosed P1} `{H2 : inputClosed P2} `{Hcomp : Comparable P1 P2} :
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
  intros x2 y; destruct (@eqP _ x2 y); crush.
  symmetry; apply leftEquiv.
  crush.

  destruct H0.
  apply RValid.
  crush.
Qed.  
