From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting.
Local Open Scope fset.


Definition all_fset {A : choiceType} (f : {fset A}) (p : A -> bool) : bool :=
  [fset x in f | p x] == f.

Lemma all_fsetP {A : choiceType} (f : {fset A}) (p : A -> bool) :
  reflect (forall (x : A), x \in f -> p x) (all_fset f p).
  apply: (iffP idP); rewrite /all_fset.
  move/eqP/fsetP => H x.
  move: (H x); rewrite !in_fset inE //=.
  destruct (x \in f).
  move/andP; elim; done.
  done.
  intro H; apply/eqP/fsetP => x.
  remember (x \in f) as b; symmetry in Heqb; destruct b.
  rewrite !in_fset !inE //= Heqb (H _ Heqb) //=.
  rewrite !in_fset !inE //= Heqb //=.
Qed.

Definition cover {A : choiceType} (f : {fset {fset A}}) : {fset A} :=
  \bigcup_(p <- f) p.

Record prePIOA {A : choiceType} :=
  {
    pQ : finType;
    cO : {fset {fset A}};
    cI : {fset {fset A}};
    cH : {fset {fset A}};
    tr :  pQ -> A -> option (Meas pQ);
    }.


Definition inputs {A : choiceType} (P : @prePIOA A) := cover (cI P).
Definition outputs {A : choiceType} (P : @prePIOA A) := cover (cO P).
Definition hiddens {A : choiceType} (P : @prePIOA A) := cover (cH P).

Definition actions {A : choiceType} (P : @prePIOA A) := inputs P `|` outputs P `|` hiddens P.
Definition lc_actions {A : choiceType} (P : @prePIOA A) := cover (cO P) `|`cover (cH P).
Definition lc_channels {A : choiceType} (P : @prePIOA A) := (cO P) `|` (cH P).
Definition channels {A : choiceType} (P : @prePIOA A) : {fset {fset A}} := cI P `|` cO P `|` cH P.

Lemma inChan_inActions {A : choiceType} (P : @prePIOA A) y T :
  T \in channels P -> y \in T -> y \in actions P.
rewrite /channels /actions //=.
move/fsetUP; elim.
move/fsetUP; elim.
intros; apply/fsetUP; left; apply/fsetUP; left.
rewrite /inputs.
rewrite /cover.
apply/bigfcupP; exists T; rewrite //=.
rewrite H //=.
intros; apply/fsetUP; left; apply/fsetUP; right; rewrite /outputs /cover; apply/bigfcupP; exists T; rewrite //= H //=.  
intros; apply/fsetUP; right; rewrite /outputs /cover; apply/bigfcupP; exists T; rewrite //= H //=.  
Qed.


Definition opt_lift {A} (p : A -> bool) := fun (x : option A) =>
                                                 match x with
                                                   | Some a => p a
                                                   | None => true
                                                               end.

Definition actionDeterm {A : choiceType} (P : @prePIOA A) (C : {fset A}) : bool :=
  all_fset C (fun a => [forall s, isSome (tr P s a) ==> all_fset C (fun b => tr P s b == None)]).

Check isSubdist.

Definition eq_rel3 {A : choiceType} (pP : @prePIOA A) :=
  [&& [disjoint (inputs pP) & (outputs pP)]%fset,
      [disjoint (inputs pP) & (hiddens pP)]%fset,
      [disjoint (outputs pP) & (hiddens pP)]%fset & 
      all_fset (channels pP) (fun C1 => all_fset (channels pP) (fun C2 => (C1 != C2) ==> [disjoint C1 & C2]%fset)) ].

Record PIOA {A : choiceType} :=
  {
    pP :> @prePIOA A;
    _ : [&&
           eq_rel3 pP,
         all_fset (inputs pP) (fun a => [forall s, tr pP s a != None]) , (* input enabled *)
         all_fset (lc_channels pP) (actionDeterm pP) & (* action determinism *)
         all_fset (actions pP) (fun a => [forall s, opt_lift isSubdist (tr pP s a)])] (* subdist *)
          }.
         

Definition PIOA_subDist {A} (P : @PIOA A) : all_fset (actions P) (fun a => [forall s, opt_lift isSubdist (tr P s a)]).
destruct P as [P Hp]; elim (and4P Hp); rewrite //=.
Qed.

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


Definition fpick {A : choiceType} (f : {fset A}) (b : A -> bool) : option A :=
  match (Sumbool.sumbool_of_bool ([fset x in f | b x] != fset0)) with
    | left Hin => Some (xchoose (fset0Pn _ Hin))
    | _ => None
             end.

Lemma fpickPt {A : choiceType} (f : {fset A}) b x :
  fpick f b = Some x -> b x /\ x \in f.
rewrite /fpick.
case: (Sumbool.sumbool_of_bool ([fset x0 | x0 in f & b x0] != fset0)) => H.
move => Heq; injection Heq => <-.
have H2 := (xchooseP (fset0Pn _ H)).
rewrite !in_fset !inE in H2.
move/andP: H2; elim; done.
done.
Qed.

Lemma fpickPn {A : choiceType} (f : {fset A}) b :
  fpick f b = None -> all_fset f (fun x => ~~ b x).
rewrite /fpick.
case: (Sumbool.sumbool_of_bool ([fset x0 | x0 in f & b x0] != fset0)) => H.
done.
move => _.
move: H.
move/negbFE/eqP/fsetP=>H.
apply/all_fsetP => x Hx.
move: (H x); rewrite !in_fset !inE //=.
rewrite Hx  andTb => -> //=.
Qed.

Inductive fpick_spec {A : choiceType} (f : {fset A}) b :=
  | fpick_true : forall x, fpick f b = Some x -> x \in f -> b x -> fpick_spec f b
  | fpick_false : fpick f b = None -> all_fset f (fun x => ~~ b x) -> fpick_spec f b.

Lemma fpickP {A : choiceType} (f : {fset A}) b : fpick_spec f b.
  remember (fpick f b); symmetry in Heqo; destruct o.
  elim (fpickPt _ _ _ Heqo) => h1 h2; eapply fpick_true.
  apply Heqo.
  apply h2.
  done.
  eapply fpick_false; rewrite //=.
  apply fpickPn; rewrite //=.
Qed.


Definition runChan {A} (P : @PIOA A) (T : {fset A}) (s : pQ P) : option (Meas (pQ P) * A) :=
  match fpick T (enabled P s) with
  | Some a =>
    match (tr P s a) with
    | Some mu => Some (mu, a)
    | None => None
    end
  | None => None
              end.

Definition Trace {Act : choiceType} (P : @PIOA Act) :=
  ((pQ P) * (list Act))%type.

Definition appChan {A} (P : @PIOA A) (C : {fset A}) (d : Meas [choiceType of Trace P]) : Meas [choiceType of Trace P] :=
  t <- d;
    match runChan P C t.1 with
      | Some (mu, a) => s' <- mu; if a \in hiddens P then ret (s', t.2) else ret (s', a :: t.2)
      | None => ret t
                    end.



Definition runPIOA {A} (P : @PIOA A) (ts : seq ({fset A})) (d : Meas ([choiceType of Trace P])) : Meas ([choiceType of Trace P]) :=
  foldl (fun acc C => appChan P C acc) d ts.

Definition closed {A} (P : @PIOA A) := cI P == fset0.

Lemma runPIOA_cons {A} (P : @PIOA A) (t : {fset A}) (ts : seq ({fset A})) d :
  runPIOA P (t :: ts) d = (runPIOA P ts (appChan P t d)).
  rewrite //=.
Qed.

Lemma runPIOA_rcons {A} (P : @PIOA A) (t : {fset A}) ts d :
  runPIOA P (rcons ts t) d = appChan P t (runPIOA P ts d).
  move: d; induction ts; rewrite //=.
Qed.

Lemma runPIOA_app {A} (P : @PIOA A) (ts ts' : seq ({fset A})) d :
  runPIOA P (ts ++ ts') d = runPIOA P ts' (runPIOA P ts d).
  rewrite /runPIOA foldl_cat //=.
Qed.


Lemma appChan_subDist {A} {P : @PIOA A} {T : {fset A}} {mu} : T \in channels P -> isSubdist mu -> isSubdist (appChan P T mu).
  rewrite /appChan => H1 H2; apply isSubdist_bind; rewrite //=.
  move => x.
  rewrite /runChan.
  case: (fpickP T (enabled P x.1)).
  move => y => -> => Henabled.
  remember (tr P x.1 y) as o; symmetry in Heqo; destruct o.
  have: isSubdist m.
  move/all_fsetP: (PIOA_subDist P).
  move/(_ y (inChan_inActions _ _ _ _ _)).
  move/(_ T H1 Henabled).
  move/forallP; move/(_ x.1).
  rewrite /opt_lift Heqo; done.
  intros; apply isSubdist_bind; rewrite //=.
  intros; destruct (y \in hiddens P); apply isSubdist_ret.
  intro; apply isSubdist_ret.
  move => -> => H; apply isSubdist_ret.
Qed.


Lemma runPIOA_subDist {A} {P : @PIOA A} {ts} {mu} : all (fun x => x \in channels P) ts -> isSubdist mu -> isSubdist (runPIOA P ts mu).
  revert mu.
induction ts; rewrite //=.
intros; apply IHts.
by elim (andP H).
apply appChan_subDist.
by elim (andP H).
done.
Qed.

(*

Lemma pIODisjoint {A}  (P : @PIOA A) :
  (forall x, x \in pO P -> fdisj (pI P) x).
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

*)