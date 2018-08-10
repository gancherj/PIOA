From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset.
Require Import Meas.
Require Import Program.
Require Import Expansion.
Require Import Posrat.
Require Import Lems.

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

Lemma enabledP {Act : finType} (P : @prePIOA Act) s a : reflect (exists mu, tr P s a = Some mu) (enabled P s a).
apply/(iffP idP).
rewrite/enabled.
remember (tr P s a) as o; symmetry in Heqo; destruct o.
intro; exists m; done.
done.
elim.
intros; rewrite /enabled.
rewrite H; done.
Qed.

Definition actionDeterm {Act : finType} (P : @prePIOA Act) (T : {set Act}) :=
  forall s x y,
    x \in T -> y \in T -> x != y -> ~~ (enabled P s x && enabled P s y).

Record ActionDisjoint {Act : finType} (pI : {set Act}) (pTO pTH : {set {set Act}}) :=
  {
    _ : forall x, x \in pTO -> [disjoint pI & x];
    _ : forall y, y \in pTH -> [disjoint pI & y];
    _ : forall x y, x \in pTO -> y \in pTH -> [disjoint x & y];
    _ : forall x y, x \in pTO -> y \in pTO -> x != y -> [disjoint x & y];
    _ : forall x y, x \in pTH -> y \in pTH -> x != y -> [disjoint x & y];
    }.
    
    

Record PIOA {Act : finType} :=
buildPIOA {
  pI : {set Act};
  pTO : {set {set Act}};
  pTH : {set {set Act}};
  pP :> @prePIOA Act;
  actionDisjoint : ActionDisjoint pI pTO pTH;
  pActionDeterm : forall T, T \in (pTO :|: pTH) -> actionDeterm pP T; 
  inputEnabled : forall s x, x \in pI -> enabled pP s x;
  actSetValid : forall s x, enabled pP s x -> x \in (pI :|: cover pTO :|: cover pTH)
  }.

Lemma pIODisjoint {A}  (P : @PIOA A) :
  (forall x, x \in pTO P -> [disjoint (pI P) & x]).
  destruct P; destruct actionDisjoint0; done.
Qed.

Lemma pIHDisjoint {A} (P : @PIOA A) :
  (forall x, x \in pTH P -> [disjoint (pI P) & x]).
  destruct P; destruct actionDisjoint0; done.
Qed.

Lemma pOHDisjoint {A} (P : @PIOA A):
  forall x y, x \in pTO P -> y \in pTH P -> [disjoint x & y].
  destruct P; destruct actionDisjoint0; done.
Qed.

Lemma pOODisjoint {A} (P : @PIOA A):
  forall x y, x \in pTO P -> y \in pTO P -> x != y -> [disjoint x & y].
  destruct P; destruct actionDisjoint0; done.
Qed.

Lemma pHHDisjoint {A} (P : @PIOA A):
  forall x y, x \in pTH P -> y \in pTH P -> x != y -> [disjoint x & y].
  destruct P; destruct actionDisjoint0; done.
Qed.


Definition action {A : finType} (P : @PIOA A) :=
  [set (pI P)] :|: (pTO P) :|: (pTH P).

Lemma pI_in_action {A : finType} (P : @PIOA A) :
  pI P \in action P.
  rewrite/action; apply/setUP; left; apply/setUP; left; rewrite in_set; done.
Qed.

Lemma tO_in_action {A : finType} (P : @PIOA A) :
  forall x, x \in pTO P -> x \in action P.
  intros; rewrite/action; apply/setUP; left; apply/setUP; right; done.
Qed.

Lemma tH_in_action {A : finType} (P : @PIOA A) :
  forall x, x \in pTH P -> x \in action P.
  intros; rewrite/action; apply/setUP; right; done.
Qed.



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

Definition isHiddenTask {A} {P : @PIOA A} (t : Task P) : bool.
destruct t.
exact (x \in pTH P).
Defined.

Definition isOutputTask {A} {P : @PIOA A} (t : Task P) : bool.
  destruct t.
  exact (x \in pTO P).
Defined.

Definition external {A} (P : @PIOA A) :=
  (pI P) :|: (cover (pTO P)).
  
Definition Trace {ActSpace : finType} (P : @PIOA ActSpace) :=
  ((pQ P) * (list ActSpace))%type.

Definition startTr {A} (P : @PIOA A) : Meas ([eqType of Trace P]) :=
  ret (start P, nil).

Definition appTask {Act : finType} (P : @PIOA Act) (T : Task P) (mu : Meas ([eqType of Trace P])) : Meas ([eqType of Trace P]) := 
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

Definition runPIOA {A} (P : @PIOA A) (ts : seq (Task P)) (d : Meas ([eqType of Trace P])) : Meas ([eqType of Trace P]) :=
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

Lemma appTask_subDist {A} {P : @PIOA A} {T} {mu} : isSubdist mu -> isSubdist (appTask P T mu).
intros.
rewrite /appTask.
dsubdist.
done.
destruct x.
case: pickP.
intros.
remember (tr P s x).
destruct o.
dsubdist.
eapply tr_subDist.
symmetry; apply Heqo.
destruct (x \in external P).
intro; dsubdist.
intro; dsubdist.
dsubdist.
intro; dsubdist.
Qed.

Lemma runPIOA_subDist {A} {P : @PIOA A} {ts} {mu} : isSubdist mu -> isSubdist (runPIOA P ts mu).
  revert mu.
induction ts.
simpl.
done.
simpl.
intros.
apply IHts.
apply appTask_subDist.
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

Check appTask.

Lemma hiddenE {A} {P : @PIOA A} (T : Task P) mu :
  isHiddenTask T -> isSubdist mu -> exists (eta : pQ P -> Meas (pQ P)),
      appTask _ T mu ~~ (t <- mu; x <- eta (fst t); ret (x, snd t)) @ 0. 
  destruct T as [Tx HT]; simpl.
  intros.
  exists ( fun s =>
             match [pick x in Tx | enabled P s x] with
             | Some a => match tr P s a with | Some mu => mu | None => ret s end
             | None => ret s
                           end).
  rewrite /appTask.
  apply measBind_cong_r; intros.
  destruct x; simpl.
  case:pickP.
  move=> x /andP; elim; move=> xin Henabled.
  remember (tr P s x) as muP.
  destruct muP.
  have: x \notin external P.
  apply/setUP.
  elim; intros.
  move/disjointP: (pIHDisjoint _ _ H).
  move/(_ _ H2).
  rewrite xin; done.
  move/bigcupP: H2; elim; intros.
  move/disjointP: (pOHDisjoint _ _ _ H2 H).
  move/(_ _ H3).
  rewrite xin; done.
  intro Hni; rewrite (negbTE Hni).
  apply measBind_cong_r; intros. reflexivity.
  eapply tr_subDist.
  symmetry; apply HeqmuP.
  dsimp; reflexivity.
  intro; dsimp; reflexivity.
  done.
Qed.

