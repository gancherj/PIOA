From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
Require Import Meas.
Require Import Program.
Require Import fset.
Require Import Expansion.
Require Import Posrat.
Require Import Lems.

Record prePIOA {Act : choiceType} :=
  mkPrePIOA {
      pQ : finType;
      start : pQ;
      tr : pQ -> Act -> option (Meas pQ);
      _ : forall s a mu, tr s a = Some mu -> isSubdist mu;
                           }.


Definition enabled {Act} (P : @prePIOA Act) (s : pQ P) :=
  fun a =>
    match (tr P s a) with | Some _ => true | None => false end.

Lemma enabledP {Act} (P : @prePIOA Act) s a : reflect (exists mu, tr P s a = Some mu) (enabled P s a).
apply/(iffP idP).
rewrite/enabled.
remember (tr P s a) as o; symmetry in Heqo; destruct o.
intro; exists m; done.
done.
elim.
intros; rewrite /enabled.
rewrite H; done.
Qed.

Definition actionDeterm {Act } (P : @prePIOA Act) (T : {fset Act}) :=
  forall s x y,
    x \in T -> y \in T -> x != y -> ~~ (enabled P s x && enabled P s y).

Record ActionDisjoint {Act : choiceType} (pI : {fset Act}) (pTO pTH : {fset {fset Act}}) :=
  {
    _ : forall x, x \in pTO -> fdisj pI x;
    _ : forall y, y \in pTH -> fdisj pI y;
    _ : forall x y, x \in pTO -> y \in pTH -> fdisj x y;
    _ : forall x y, x \in pTO -> y \in pTO -> x != y -> fdisj x y;
    _ : forall x y, x \in pTH -> y \in pTH -> x != y -> fdisj x y;
    }.
    

Definition cover {A : choiceType} (X : {fset {fset A}}) : {fset A} :=
  \bigcup_(x in X) x.
    

Record PIOA {Act : choiceType} :=
buildPIOA {
  pI : {fset Act};
  pTO : {fset {fset Act}};
  pTH : {fset {fset Act}};
  pP :> @prePIOA Act;
  actionDisjoint : ActionDisjoint pI pTO pTH;
  pActionDeterm : forall T, T \in (pTO `|` pTH) -> actionDeterm pP T; 
  inputEnabled : forall s x, x \in pI -> enabled pP s x;
  actSetValid : forall s x, enabled pP s x -> x \in (pI `|` cover pTO `|` cover pTH)
  }.

Lemma pIODisjoint {A}  (P : @PIOA A) :
  (forall x, x \in pTO P -> fdisj (pI P) x).
  destruct P; destruct actionDisjoint0; done.
Qed.

Lemma pIHDisjoint {A} (P : @PIOA A) :
  (forall x, x \in pTH P -> fdisj (pI P) x).
  destruct P; destruct actionDisjoint0; done.
Qed.

Lemma pOHDisjoint {A} (P : @PIOA A):
  forall x y, x \in pTO P -> y \in pTH P -> fdisj x y.
  destruct P; destruct actionDisjoint0; done.
Qed.

Lemma pOODisjoint {A} (P : @PIOA A):
  forall x y, x \in pTO P -> y \in pTO P -> x != y -> fdisj x y.
  destruct P; destruct actionDisjoint0; done.
Qed.

Lemma pHHDisjoint {A} (P : @PIOA A):
  forall x y, x \in pTH P -> y \in pTH P -> x != y -> fdisj x y.
  destruct P; destruct actionDisjoint0; done.
Qed.


Definition action {A} (P : @PIOA A) :=
  [fset (pI P)] `|` (pTO P) `|` (pTH P).

Lemma pI_in_action {A} (P : @PIOA A) :
  pI P \in action P.
  rewrite/action; apply/fsetUP; left; apply/fsetUP; left; rewrite in_fset; done.
Qed.

Lemma tO_in_action {A} (P : @PIOA A) :
  forall x, x \in pTO P -> x \in action P.
  intros; rewrite/action; apply/fsetUP; left; apply/fsetUP; right; done.
Qed.

Lemma tH_in_action {A} (P : @PIOA A) :
  forall x, x \in pTH P -> x \in action P.
  intros; rewrite/action; apply/fsetUP; right; done.
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

Definition Tasks {Act} (P : @PIOA Act) := (pTO P) `|` (pTH P).

Definition Task (Act : choiceType) := {fset Act}.

Definition runTask {A} {P : @PIOA A} (T : Task A) (s : pQ P) : option (Meas (pQ P) * A) :=
  match fpick (enabled P s) T with
  | Some a =>
    match (tr P s a) with
    | Some mu => Some (mu, a)
    | None => None
    end
  | None => None
              end.

Definition external {A} (P : @PIOA A) :=
  (pI P) `|` (cover (pTO P)).
  
Definition Trace {Act} (P : @PIOA Act) :=
  ((pQ P) * (list Act))%type.

Definition appTask {A} (P : @PIOA A) (T : Task A) (mu : Meas [eqType of Trace P]) : Meas [eqType of Trace P] :=
  t <- mu;
    match (runTask T t.1) with
    | Some p => s <- p.1; if (p.2 \in (external P)) then ret (s, p.2 :: t.2) else ret (s, t.2)
    | None => ret t
                  end.

Definition startTr {A} (P : @PIOA A) : Meas ([eqType of Trace P]) :=
  ret (start P, nil).


Lemma appTask_distrib {A} (P : @PIOA A) (T : Task A) :
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

Lemma appTask_cong {A} (P : @PIOA A) : forall (T : Task A),
  measCong (appTask P T).
  unfold measCong, appTask; intros; dsimp.
  drewr (measBind_cong_l H).
  intros.
  destruct x; intros.
  rewrite /runTask; simpl.
  case: fpickP; intros.
  remember (tr P s x) as mu; symmetry in Heqmu; destruct mu; dsubdist.
  simpl.
  intro x0; caseOn (x \in external P); intro Heq.
  rewrite Heq; dsubdist.
  rewrite (negbTE Heq); dsubdist.
  dsubdist.
  dsimp.
Qed.

Definition runPIOA {A} (P : @PIOA A) (ts : seq (Task A)) (d : Meas ([eqType of Trace P])) : Meas ([eqType of Trace P]) :=
  foldl (fun acc t => appTask P t acc) d ts.

Lemma runPIOA_cons {A} (P : @PIOA A) (t : Task A) (ts : seq (Task A)) d :
  runPIOA P (t :: ts) d = (runPIOA P ts (appTask P t d)).
  unfold runPIOA.
  simpl.
  auto.
Qed.

Lemma runPIOA_rcons {A} (P : @PIOA A) (t : Task A) ts d :
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


Lemma runPIOA_app {A} (P : @PIOA A) (ts ts' : seq (Task A)) d :
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

Lemma appTask_subDist {A} {P : @PIOA A} {T : Task A} {mu} : isSubdist mu -> isSubdist (appTask P T mu).
intros.
rewrite /appTask.
dsubdist.
done.
destruct x.
rewrite /runTask //=.
case: fpickP.
intros.
remember (tr P s x).
destruct o.
dsubdist.
eapply tr_subDist.
symmetry; apply Heqo.
simpl; caseOn (x \in external P); intro Heqb; [rewrite Heqb | rewrite (negbTE Heqb)]; intros.
dsubdist.
dsubdist.
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
  (pI P) = fset0.

Definition inputEquiv {A} (P1 P2 : @PIOA A) :=
  (pI P1) = (pI P2).

Definition hiddenTask {A} (P : @PIOA A) : Task A -> bool := fun T => (T) \in pTH P.

Definition outputTask {A} (P : @PIOA A) : Task A -> bool := fun T => (T) \in pTO P.

Definition isTask {A} (P : @PIOA A) : Task A -> bool := fun T => T \in Tasks P.

Definition refinement {A} (P1 P2 : @PIOA A)  `{inputClosed P1} `{inputClosed P2} e :=
  forall ts, all (isTask P1) ts -> exists ts',
      all (isTask P2) ts' /\
      traceOf (runPIOA P1 ts (startTr P1)) ~~ traceOf (runPIOA P2 ts' (startTr P2)) @ e.




Lemma hiddenP {A} {P : @PIOA A} (T : Task A) mu :
  hiddenTask P T -> isSubdist mu -> exists (eta : pQ P -> Meas (pQ P)),
      appTask P T mu ~~ (t <- mu; x <- eta (fst t); ret (x, snd t)) @ 0. 

  intros.
  exists ( fun s =>
             match fpick (enabled P s) T with
             | Some a => match tr P s a with | Some mu => mu | None => ret s end
             | None => ret s
                           end).
  rewrite /appTask /runTask.
  apply measBind_cong_r; intros.
  destruct x; simpl.
  case:fpickP.
  intros.
  remember (tr P s x) as muP.
  destruct muP.
  simpl.

  have: x \notin external P.
  apply/fsetUP.
  elim; intros.
  move/fdisjointP: (pIHDisjoint _ _ H).
  move/(_ _ H2).
  rewrite i0; done.

  elim: (cupP _ _ _ _ H2) => x0; move/andP; elim; intros.
  move/fdisjointP: (pOHDisjoint _ _ _ H3 H).
  elim: (andP H4) => _ h4.
  move/(_ _ H4).
  rewrite i0; done.
  intro Hni.
  rewrite /runTask //=.
  rewrite (negbTE Hni).
  apply measBind_cong_r; intros. reflexivity.
  eapply tr_subDist.
  symmetry; apply HeqmuP.
  dsimp; reflexivity.
  intro; dsimp; reflexivity.
  done.
Qed.

