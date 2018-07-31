From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset.
Require Import Meas.
Require Import Program.
Require Import Expansion.
Require Import Posrat.

Record prePIOA {Act : finType} :=
  mkPrePIOA {
      pQ : finType;
      start : pQ;
      tr : pQ -> Act -> option (Meas pQ);
      _ : forall s a mu, tr s a = Some mu -> isSubdist mu;
                           }.


Definition enabled {Act : finType} (P : @prePIOA Act) (s : pQ P) :=
  fun a =>
    match (tr P s a) with | Some _ => true | None => false end.


Definition actionDeterm {Act : finType} (P : @prePIOA Act) (T : {set Act}) :=
  forall s x y,
    x \in T -> y \in T -> x != y -> ~~ (enabled P s x && enabled P s y).

Record PIOA {Act : finType} :=
mkPIOA {
  pI : {set Act};
  pTO : {set {set Act}};
  pTH : {set {set Act}};
  pP :> @prePIOA Act;
  actionDisjoint : trivIset ([set pI] :|: pTO :|: pTH);
  pActionDeterm : forall T, T \in (pTO :|: pTH) -> actionDeterm pP T;
  inputEnabled : forall s x, x \in pI -> enabled pP s x;
  actSetValid : forall s x, enabled pP s x -> x \in (pI :|: (cover pTO :|: cover pTH))
  }.

Definition action {A} (P : @PIOA A) :=
  (pI P) :|: (cover (pTO P)) :|: (cover (pTH P)).


Lemma tr_subDist {A} (P : @PIOA A) s a mu :
  tr P s a = Some mu ->
  isSubdist mu.
intros.
destruct P.
destruct pP0.
eapply i.
apply H.
Qed.

Definition Task {Act : finType} (P : @PIOA Act) := {x : {set Act} | x \in (pTO P) :|: (pTH P)}.

Definition external {A} (P : @PIOA A) :=
  (pI P) :|: (cover (pTO P)).
  
Definition Trace {ActSpace} (P : @PIOA ActSpace) :=
  [eqType of ((pQ P) * (list ActSpace))%type].

Definition startTr {A} (P : @PIOA A) : Meas (Trace P) :=
  ret (start P, nil).

Definition appTask {Act : finType} (P : @PIOA Act) (T : Task P) (mu : Meas (Trace P)) : Meas (Trace P) := 
  t <- mu;
  let (s, actions) := t in
  match [pick x in (sval T) | enabled P s x] with
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
  unfold joinDistrib, appTask; intros; dsimp.
  apply measEquiv_refl.
Qed.

Ltac dsubdist := repeat (
  match goal with
  | [ |- is_true (isSubdist (ret _)) ] => apply isSubdist_ret
  | [ |- is_true (isSubdist (_ <- _; _)) ] => apply isSubdist_bind
  | [ H : tr _ _ _ = Some ?m |- is_true (isSubdist ?m) ] => eapply tr_subDist; apply H
 end).

Lemma appTask_cong {A} (P : @PIOA A) : forall (T : Task P),
  measCong (appTask P T).
  unfold measCong, appTask; intros; dsimp.
  drewr (measBind_cong_l H).
  intros.
  destruct x; intros.
  case: pickP; intros.
  remember (tr P s x) as mu; symmetry in Heqmu; destruct mu; dsubdist.
  intro x0; destruct (x \in external P); dsubdist.
  dsubdist.
  dsimp.
Qed.

Definition runPIOA {A} (P : @PIOA A) (ts : seq (Task P)) (d : Meas (Trace P)) : Meas (Trace P) :=
  foldl (fun acc t => appTask P t acc) d ts.

Lemma runPIOA_cons {A} (P : @PIOA A) (t : Task P) (ts : seq (Task P)) d :
  runPIOA P (t :: ts) d = (runPIOA P ts (appTask P t d)).
  unfold runPIOA.
  simpl.
  auto.
Qed.

Lemma runPIOA_rcons {A} (P : @PIOA A) (t : Task P) ts d :
  runPIOA P (rcons ts t) d = appTask P t (runPIOA P ts d).
  move: d.
  induction ts.
  simpl.
  done.
  simpl.
  intros.
  rewrite IHts.
  done.
Qed.

Lemma runPIOA_app {A} (P : @PIOA A) (ts ts' : seq (Task P)) d :
  runPIOA P (ts ++ ts') d = runPIOA P ts' (runPIOA P ts d).
  unfold runPIOA; rewrite foldl_cat.
  done.
Qed.

Lemma runPIOA_cong {A} (P : @PIOA A) ts :
  measCong (runPIOA P  ts).
  unfold measCong, runPIOA; intros.
  move: ts.
  apply last_ind.
  simpl; done.
  intros; simpl; rewrite -!cats1 !foldl_cat //=.
  drewr (appTask_cong P).
  apply H0.
  dsimp.
Qed.
      
  
Lemma runPIOA_distrib {A} {P : @PIOA A} ts :
  joinDistrib (runPIOA P ts).
  move: ts. apply last_ind.
  rewrite /joinDistrib /runPIOA //=.
  intros.
  unfold joinDistrib in *.
  dsimp.
  rewrite /joinDistrib; intros.
  rewrite runPIOA_rcons.
  drewr (appTask_cong P).
  apply H.
  rewrite /appTask; dsimp.
  done.
  rewrite /appTask; dsimp.
  apply measBind_cong_r; intros.
  rewrite runPIOA_rcons /appTask.
  apply measEquiv_refl.
  done.
Qed.

Definition traceOf {Q act : eqType} (D : Meas ([eqType of Q * list act])%type) :=
  meas_fmap D snd.

Definition inputClosed {A} (P : @PIOA A) :=
  (pI P) = set0.

Definition inputEquiv {A} (P1 P2 : @PIOA A) :=
  (pI P1) = (pI P2).

Definition refinement {A} (P1 P2 : @PIOA A)  `{inputClosed P1} `{inputClosed P2} e :=
  forall ts, exists ts',
      traceOf (runPIOA P1 ts (startTr P1)) ~~ traceOf (runPIOA P2 ts' (startTr P2)) @ e.

(*
Definition consistent {A} {P : @PIOA A} (d1 : Meas (Trace P)) (ts : seq (Task P)) (d2 : Meas (Trace P)) :=
  forall p, p \in measSupport d2 -> p \in measSupport (runPIOA P ts d1).

Lemma consistent_cons {A} {P : @PIOA A} (ts : seq (Task P)) (t : Task P) (d1 d3 : Meas (Trace P)) :
  consistent d1 (t :: ts) d3 -> exists d2,
    consistent d1 [:: t] d2 /\ consistent d2 ts d3.
intros.
rewrite /consistent in H; simpl in H.

exists (appTask _ t d1).
rewrite /consistent; split.
intros.
simpl.
done.
intros.
apply H.
done.
Qed.


Record SimR {A} (P1 P2 : @PIOA A) 
       (R : Meas ([eqType of Trace P1]) -> Meas (Trace P2) -> Prop) :=
  {
    simStart : R (ret (start P1, nil)) (ret (start P2, nil));
    simTr : forall d1 d2, R d1 d2 -> traceOf d1 ~~ traceOf d2;
    simStep : forall ts T, exists ts', forall d1 d2, consistent (startTr _) ts d1 -> R d1 d2 ->
          (expansion R) (appTask P1 T d1) (runPIOA P2 ts' d2)}.


Lemma fmap_cong {A B : eqType} (d1 d2 : Meas A) (f : A -> B) :
  d1 ~~ d2 -> meas_fmap d1 f ~~ meas_fmap d2 f.
  intros. unfold meas_fmap.
  rewrite (measBind_cong_l H).
  apply measEquiv_refl.
Qed.
  

Lemma expansion_trace : forall {Q Q' act : eqType} (R : Meas ([eqType of Q * list act]%type) -> Meas ([eqType of Q' * list act]%type) -> Prop) d1 d2, (forall d1 d2, R d1 d2 -> traceOf d1 ~~ traceOf d2) -> expansion R d1 d2 -> traceOf d1 ~~ traceOf d2.
  intros.
  destruct H0.
  destruct H0.
  unfold traceOf.
  rewrite (fmap_cong _ _ _ leftEquiv).
  rewrite (fmap_cong _ _ _ rightEquiv).
  unfold meas_fmap.
  dsimp.
  apply measBind_cong_r; intros.
  apply H.
  apply RValid.
  done.
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
  done.
  done.

  move: ts; apply last_ind.
  exists nil.
  exists (ret (ret (start P1, nil), ret (start P2, nil))).
  constructor.
  simpl; rewrite bindRet; simpl; unfold startTr; unfold measEquiv; done.
  simpl; rewrite bindRet; simpl; unfold startTr; unfold measEquiv; done.
  intros.
  simpl in H0.
  rewrite /measSupport in H0.
  simpl in H0.
  rewrite in_cons in H0.
  move/orP: H0.
  elim.
  move/eqP => Hp.
  subst; simpl.
  apply simStart0.
  done.
  intros.
  destruct H0.
  destruct H0.
  destruct H0.
  
  destruct (simStep0 s x).
  simpl.
  exists (x0 ++ x2).
  rewrite runPIOA_rcons.
  rewrite runPIOA_app.
  eapply joinDistrib_expansion_compat.
  apply appTask_cong.
  apply appTask_distrib.
  apply runPIOA_cong.
  apply runPIOA_distrib.
  constructor.
  rewrite leftEquiv.
  rewrite /meas_fmap.
  dsimp.
  apply measBind_cong_r; intros; dsimp.
  rewrite rightEquiv.
  rewrite /meas_fmap.
  dsimp.
  apply RValid.
  rewrite /meas_fmap.
  dsimp.
  rewrite leftEquiv.
  apply measBind_cong_r; intros; dsimp.
  rewrite rightEquiv /meas_fmap.
  dsimp.
  apply measBind_cong_r; intros; dsimp.
  intros.
  simpl in p.
  apply H0.
  rewrite /consistent.
  intros.
  eapply measSupport_measEquiv.
  symmetry; apply leftEquiv.
  apply measBind_in.
  exists p.
  apply/andP; done.
  apply RValid.
  done.
Qed.  
*)