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
    start : pQ;
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
  all_fset C (fun a => [forall s, isSome (tr P s a) ==> all_fset C (fun b => (a != b) ==> (tr P s b == None))]).

Check isSubdist.

Definition eq_rel3 {A : choiceType} (pP : @prePIOA A) :=
  [&& [disjoint (inputs pP) & (outputs pP)]%fset,
      [disjoint (inputs pP) & (hiddens pP)]%fset,
      [disjoint (outputs pP) & (hiddens pP)]%fset & 
      all_fset (channels pP) (fun C1 => all_fset (channels pP) (fun C2 => (C1 != C2) ==> [disjoint C1 & C2]%fset)) ].

Definition PIOA_axiom {A : choiceType} (pP : @prePIOA A) :=
     [&&
           eq_rel3 pP,
         all_fset (inputs pP) (fun a => [forall s, tr pP s a != None]) , (* input enabled *)
         all_fset (lc_channels pP) (actionDeterm pP) & (* action determinism *)
         all_fset (actions pP) (fun a => [forall s, opt_lift isSubdist (tr pP s a)])]. (* subdist *)

Record PIOA {A : choiceType} :=
  {
    pP :> @prePIOA A;
    _ : PIOA_axiom pP
                   }.


Record PIOAProps {A : choiceType} (pP : @prePIOA A) :=
  {
    _ : forall a, a \in inputs pP -> a \notin outputs pP;
    _ : forall a, a \in outputs pP -> a \notin inputs pP;
    _ : forall a, a \in inputs pP -> a \notin hiddens pP;
    _ : forall a, a \in hiddens pP -> a \notin inputs pP;
    _ : forall a, a \in outputs pP -> a \notin hiddens pP;
    _ : forall a, a \in hiddens pP -> a \notin outputs pP;
    _ : forall c1 c2, c1 \in channels pP -> c2 \in channels pP -> c1 != c2 -> [disjoint c1 & c2]%fset;
    _ : forall a, a \in inputs pP -> forall s, tr pP s a != None;
    _ : forall c, c \in lc_channels pP -> forall a b, a \in c -> b \in c -> forall s, a != b -> isSome (tr pP s a) -> tr pP s b = None;
    _ : forall a s, a \in actions pP -> opt_lift isSubdist (tr pP s a)
                             }.

Lemma PIOAP {A} (P : @PIOA A) : PIOAProps P.
  destruct P as [P Hp].
elim: (and4P Hp).
move/and4P; elim; intros.
  constructor; intros.
apply (fdisjointP H); rewrite //=.
rewrite fdisjoint_sym in H; apply (fdisjointP H); rewrite //=.
apply (fdisjointP H0); rewrite //=.
rewrite fdisjoint_sym in H0; apply (fdisjointP H0); rewrite //=.
apply (fdisjointP H1); rewrite //=.
rewrite fdisjoint_sym in H1; apply (fdisjointP H1); rewrite //=.
move/all_fsetP: H2; move/(_ c1 H6).
move/all_fsetP; move/(_ c2 H7).
move/implyP/(_ H8); done.
move/all_fsetP: H3; move/(_ a H6)/forallP/(_ s); done.
move/all_fsetP: H4; move/(_ c H6).
move/all_fsetP; move/(_ a H7).
move/forallP; move/(_ s); move/implyP; move/(_ H10).
move/all_fsetP; move/(_ b H8).
move/implyP; move/(_ H9)/eqP; done.
move/all_fsetP: H5; move/(_ a H6)/forallP/(_ s); done.
Qed.


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

Definition startTr {A} (P : @PIOA A) : Meas [choiceType of Trace P] :=
  ret (start P, nil).

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

Definition traceOf {A} {P : @PIOA A} (m : Meas [choiceType of Trace P]) := measMap m snd.

Definition refinement {A} (P1 P2 : @PIOA A) (H1 : closed P1) (H2 : closed P2) :=
  forall (ts : seq {fset A}), all (fun x => x \in channels P1) ts ->
                              exists (ts' : seq {fset A}), all (fun x => x \in channels P2) ts' /\
                                                           (traceOf (runPIOA P1 ts (startTr P1)) = traceOf (runPIOA P2 ts' (startTr P2))).

Lemma refinement_refl {A} (P : @PIOA A) (H1 : closed P) : refinement P P H1 H1.
  move => ts Hts; exists ts; split; done.
Qed.

Lemma refinement_trans {A} (P1 P2 P3 : @PIOA A) (H1 : closed P1) (H2 : closed P2) (H3 : closed P3) : refinement P1 P2 H1 H2 -> refinement P2 P3 H2 H3 -> refinement P1 P3 H1 H3.
  move => R1 R2 ts Hts.
  elim (R1 ts Hts) => ts' [Hts' Htr].
  elim (R2 ts' Hts') => ts'' [Hts'' Htr'].
  exists ts''; split; rewrite ?Htr //=.
Qed.

Lemma PIOAAxiom {A} (P : @PIOA A) : PIOA_axiom P.
  destruct P; done.
Qed.