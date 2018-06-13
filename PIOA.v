Add LoadPath "~/fcf/src".
Require Import Meas.
Require Import Program.
Require Import Expansion.
Require Import FCF.Rat.
Require Import Ring.
Require Import List.
Require Import CpdtTactics.

Record PIOA {acts : Set} {tasks : Set} :=
  mkPIOA {
      pQ : Set;
      start : pQ;
      trT : pQ -> tasks -> option (Meas (pQ * option acts));
      trI : pQ -> acts -> option (Meas pQ);
      }.


Definition startTr {act tasks : Set} (P : @PIOA act tasks) : Meas ((pQ P) * (list act)) :=
  ret (start P, nil).

Definition appTask {act task : Set} (P : @PIOA act task) (T : task) (TrD : Meas ((pQ P) * (list act))) : Meas (pQ P * list act) :=
  Tr <- TrD;
  match trT P (fst Tr) T with
  | Some mu =>
    x <- mu;
      match x with
        | (s, Some a) => ret (s, a :: (snd Tr))
        | (s, None) => ret (s, snd Tr)
                           end
  | None => ret Tr
                end.

Lemma appTask_distrib {act task : Set} {P : @PIOA act task} {T : task} :
  joinDistrib (appTask P T).
  unfold joinDistrib; intros.
  unfold appTask.
  unfold fmap.
  repeat rewrite bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet.
  apply measEquiv_refl.
Qed.

Lemma appTask_cong {act task : Set} {P : @PIOA act task} {T : task} :
  measCong (appTask P T).
  unfold measCong, appTask; intros.
    rewrite (measBind_cong_l H).
    unfold measEquiv; crush.
Qed.

Definition runPIOA {act task : Set} (P : @PIOA act task) (ts : list task) (d : Meas (pQ P * list act)) :=
  fold_right (fun t acc => appTask P t acc) d ts.

Lemma runPIOA_cons {act task : Set} (P : @PIOA act task) (t : task) (ts : list task) d :
  runPIOA P (t :: ts) d = appTask P t (runPIOA P ts d).
  unfold runPIOA.
  simpl.
  auto.
Qed.

Lemma runPIOA_app {act task : Set} (P : @PIOA act task) (ts ts' : list task) d :
  runPIOA P (ts ++ ts') d = runPIOA P ts (runPIOA P ts' d).
  unfold runPIOA.
  rewrite fold_right_app.
  auto.
Qed.

Lemma runPIOA_cong {act task : Set} (P : @PIOA act task) ts :
  measCong (runPIOA P  ts).
  unfold measCong, runPIOA; intros.
  induction ts.
  simpl.
  crush.
  simpl.
  rewrite (appTask_cong _ _ IHts).
  apply measEquiv_refl.
Qed.
      
  
Lemma runPIOA_distrib {act task : Set} {P : @PIOA act task} ts :
  joinDistrib (runPIOA P ts).
  unfold joinDistrib.
  intros.
  induction ts.
  simpl.
  unfold runPIOA; simpl.
  unfold fmap.
  rewrite bindAssoc.
  apply measBind_cong_r; intros.
  rewrite bindRet.
  unfold measEquiv; crush.
  rewrite runPIOA_cons.
  rewrite (appTask_cong _ _ IHts).
  unfold fmap.
  unfold appTask.
  repeat rewrite bindAssoc.
  apply measBind_cong_r; intros.
  repeat rewrite bindRet.
  rewrite runPIOA_cons.
  unfold appTask.
  unfold measEquiv; crush.
Qed.

Definition traceOf {Q act : Set} (D : Meas (Q * list act)):=
  fmap D snd.

Definition inputEquiv {act T T' : Set} (P1 : @PIOA act T) (P2 : @PIOA act T') :=
  forall i s t,
    trI P1 s i = None <-> trI P2 t i = None.

Definition inputClosed {act task : Set} (P : @PIOA act task) :=
  forall i s,
    trI P s i = None.

(* This covers output and hidden disjointness *)
Record compatiblePIOA {act task : Set} (P1 P2 : @PIOA act task) :=
  {
    (* We can also just say that the task set for P1 and P2 are always considered distinct, since they will have 'inl' and 'inr' attached to them in the composite. *)
    taskDisjL : forall T s t mu1,
      trT P1 s T = Some mu1 -> trT P2 t T = None;
    taskDisjR : forall T s t mu2,
        trT P2 t T = Some mu2 -> trT P1 s T = None;
    outDisj : forall T T2 s t mu1 mu2 a,
        trT P1 s T = Some mu1 -> trT P2 t T2 = Some mu2 ->
        ~ (In a (map snd (measSupport mu1)) /\
           In a (map snd (measSupport mu2)))}.

Definition refinement {act T T' : Set} (P1 : @PIOA act T) (P2 : @PIOA act T') `{inputClosed P1} `{inputClosed P2} :=
  forall ts, exists ts',
      traceOf (runPIOA P1 ts (startTr P1)) ~~ traceOf (runPIOA P2 ts' (startTr P2)).

Record SimR {act task task' : Set} (P1 : @PIOA act task) (P2 : @PIOA act task')
       (R : Meas (pQ P1 * list act) -> Meas (pQ P2 * list act) -> Prop) :=
  {
    simStart : R (ret (start P1, nil)) (ret (start P2, nil));
    simTr : forall d1 d2, R d1 d2 -> traceOf d1 ~~ traceOf d2;
    (* no history yet *)
    simStep : forall T, exists ts, forall d1 d2, R d1 d2 ->
          (expansion R) (appTask P1 T d1) (runPIOA P2 ts d2)}.


Lemma expansion_trace : forall {Q Q' act : Set} (R : Meas (Q * list act) -> Meas (Q' * list act) -> Prop) d1 d2, (forall d1 d2, R d1 d2 -> traceOf d1 ~~ traceOf d2) -> expansion R d1 d2 -> traceOf d1 ~~ traceOf d2.
  intros.
  destruct H0.
  destruct H0.
  unfold traceOf.
  rewrite (meas_fmap_cong leftEquiv).
  rewrite (meas_fmap_cong rightEquiv).
  unfold fmap.
  repeat rewrite bindAssoc.
  apply measBind_cong_r; intros.
  apply H.
  apply RValid.
  crush.
Qed.
  
Lemma simSound {act task task' : Set} (P1 : @PIOA act task) (P2 : @PIOA act task') R `{H: inputClosed P1} `{H2 : inputClosed P2} :
  SimR P1 P2 R -> @refinement _ _ _ P1 P2 H H2.
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
  destruct (simStep0 a).
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
  unfold fmap.
  rewrite bindAssoc; apply measBind_cong_r; intros; rewrite bindRet; unfold measEquiv; crush.
  destruct H0.
  rewrite rightEquiv; unfold fmap;
  rewrite bindAssoc; apply measBind_cong_r; intros; rewrite bindRet; unfold measEquiv; crush.
  intros; apply H1.
  destruct H0.
  apply RValid.
  crush.
Qed.  
