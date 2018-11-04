From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting Aux FastEnum.
Local Open Scope fset.



Record prePIOA {A : choiceType} :=
  {
    pQ : fastEnumType;
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
  all_fset (fun a => [forall s, isSome (tr P s a) ==> all_fset (fun b => (a != b) ==> (tr P s b == None)) C]) C.

Check isSubdist.

Definition eq_rel3 {A : choiceType} (pP : @prePIOA A) :=
  [&& [disjoint (inputs pP) & (outputs pP)]%fset,
      [disjoint (inputs pP) & (hiddens pP)]%fset,
      [disjoint (outputs pP) & (hiddens pP)]%fset & 
      all_fset  (fun C1 => all_fset (fun C2 => (C1 != C2) ==> [disjoint C1 & C2]%fset) (channels pP)) (channels pP)].

Definition PIOA_axiom {A : choiceType} (pP : @prePIOA A) :=
     [&&
           eq_rel3 pP,
         all_fset (fun a => [forall s, tr pP s a != None]) (inputs pP) , (* input enabled *)
         all_fset (actionDeterm pP) (lc_channels pP) & (* action determinism *)
         all_fset (fun a => [forall s, opt_lift isSubdist (tr pP s a)]) (actions pP)]. (* subdist *)

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


Definition PIOA_subDist {A} (P : @PIOA A) : all_fset (fun a => [forall s, opt_lift isSubdist (tr P s a)]) (actions P).
destruct P as [P Hp]; elim (and4P Hp); rewrite //=.
Qed.

Print isSome.

Definition enabled {Act} (P : @prePIOA Act) (s : pQ P) :=
  fun a => isSome (tr P s a).

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


(* Mechanism for definition of PIOA & automatic checking *)


Definition channels_of_seqs {A : choiceType} (s : seq (seq A)) : {fset {fset A}} :=
  fset_of_seq (map fset_of_seq s).


Lemma channels_of_seqs_U {A : choiceType} (s1 s2 : seq (seq A)) :
  (channels_of_seqs s1 `|` channels_of_seqs s2)%fset = channels_of_seqs (s1 ++ s2).
  rewrite /channels_of_seqs.
  rewrite map_cat fset_of_seq_cat //=.
Qed.

Lemma all_fset_cover_seq {A : choiceType} (s : seq (seq A)) P :
  all P (flatten s) = all_fset P (cover (channels_of_seqs s)).

  apply Bool.eq_true_iff_eq; split.
  rewrite all_flatten.
  move/allP => H.
  apply/all_fsetP => x Hx.
  elim (bigfcupP _ _ _ _ Hx) => y Hy1 Hy2.
  rewrite andbT in Hy1.
  rewrite -in_fset_of_seq in Hy1.
  move/mapP: Hy1; elim => X HX1 HX2.
  move/allP: (H _ HX1). 
  rewrite HX2 -in_fset_of_seq in Hy2.
  move/(_ _ Hy2); done. 


  move/all_fsetP => H.
  rewrite all_flatten; apply/allP => x Hx; apply/allP => y Hy.
  apply H.
  apply/bigfcupP.
  exists (fset_of_seq x).
  rewrite -in_fset_of_seq andbT; apply/mapP; exists x; rewrite //=.

  rewrite -in_fset_of_seq //=.
Qed.

Definition fdisj_seq {A : choiceType} (s1 s2 : (seq A)) :=
  all (fun x => all (fun y => x != y) s2) s1.

Lemma fdisj_seqP {A : choiceType} (s1 s2 : (seq A)) :
  fdisj_seq s1 s2 -> [disjoint (fset_of_seq s1) & (fset_of_seq s2)].
  move/allP => H.
  apply/fdisjointP => a Ha.
  rewrite -in_fset_of_seq; rewrite -in_fset_of_seq in Ha.
  move/allP: (H a Ha) => H2. 
  apply/contraT; rewrite negbK => Hc.
  move: (H2 _ Hc); rewrite eq_refl //=.
Qed.

Lemma fdisj_cover_seqP {A : choiceType} (s1 s2 : seq (seq A)) :
  fdisj_seq (flatten s1) (flatten s2) -> [disjoint (cover (channels_of_seqs s1))  & (cover (channels_of_seqs s2))]%fset.
  move/fdisj_seqP.
  rewrite !fset_of_seq_flatten /cover /channels_of_seqs //=.
Qed.

Definition channels_pairwise_disj {A : choiceType} (s : seq (seq A)) :=
  all (fun C => all (fun C' => (C != C') ==> (fdisj_seq C C')) s) s.
(*  foldr (fun C acc => acc && foldr (fun C' acc2 => acc2 && ((C != C') ==> (fdisj_seq C C'))) true s) true s. *)

Lemma channels_pairwise_disjP {A : choiceType} (s : seq (seq A)) :
  channels_pairwise_disj s -> all_fset (fun C => all_fset (fun C' => (C != C') ==> ([disjoint C & C']%fset)) (channels_of_seqs s)) (channels_of_seqs s).
  move/allP => H.
  apply/all_fsetP  => x Hx.
  apply/all_fsetP  => y Hy.
  apply/implyP => Hneq.
  rewrite -in_fset_of_seq in Hx; elim (mapP Hx) => zx Hzx Hzx'.
  rewrite -in_fset_of_seq in Hy; elim (mapP Hy) => zy Hzy Hzy'.
  subst.
  apply fdisj_seqP.
  move/allP: (H _ Hzx).
  move/(_ _ Hzy);move/implyP.
  case (eqVneq zx zy).
  move => Hc; rewrite Hc eq_refl in Hneq; rewrite //=.
  move => Hn; move/(_ Hn); rewrite //=.
Qed.

Definition decide_inputenabled {A : choiceType} (C : seq A) (P : @prePIOA A) :=
  all (fun a => all (fun s => tr P s a != None) (@fastEnum (pQ P))) C.

Lemma decide_inputenabledP {A : choiceType} (C : seq (seq A)) (P : @prePIOA A) :
  decide_inputenabled (flatten C) P -> all_fset (fun a => [forall s, tr P s a != None]) (cover (channels_of_seqs C)).
  move/allP => H.
  apply/all_fsetP => x Hx.
  apply/forallP => s.
  move/bigfcupP: Hx; elim => z Hz1 Hz2.
  rewrite andbT -in_fset_of_seq in Hz1; move/mapP: Hz1; elim => y Hy H'; subst.
  have: x \in flatten C.
  apply/flattenP; exists y; rewrite //=.
  rewrite in_fset_of_seq //=.
  move => Hf; move/allP: (H _ Hf) => H2.
  apply H2.
  apply mem_fastEnum.
Qed.

Definition decide_actionDeterm {A : choiceType} (Cs : seq (seq A)) (P : @prePIOA A) :=
  all (fun C => all (fun a => all (fun s => tr P s a ==> (all (fun b => (a != b) ==> (tr P s b == None)) C)) (fastEnum (pQ P))) C) Cs.

Definition channels_allpairs {A : choiceType} (Cs : seq (seq A)) : seq (A * A)  :=
  flatten (map (fun C => allpairs (fun x y => (x,y)) C C) Cs).                                                                     

Definition decide_actionDeterm_flat {A : choiceType} (Cs : seq (seq A)) (P : @prePIOA A) :=
  all (fun abs => tr P abs.2 abs.1.1 ==> (abs.1.1 != abs.1.2) ==> (tr P abs.2 abs.1.2 == None))
      (allpairs (fun x y => (x,y)) (channels_allpairs Cs) (fastEnum (pQ P))).

Lemma decide_actionDeterm_flatE {A : choiceType} (Cs : seq (seq A)) (P : @prePIOA A) :
  decide_actionDeterm Cs P = decide_actionDeterm_flat Cs P.
  rewrite /decide_actionDeterm /decide_actionDeterm_flat.
  apply Bool.eq_true_iff_eq; split => H.
  apply/allP => abs.
  move/allpairsP; elim => abs'; elim => H1 H2 => ->.
  simpl.
  apply/implyP => Htr; apply/implyP => Hneq.
  move/flattenP: H1; elim => ab.
  move/mapP; elim => C HC HC2; subst.
  move/allpairsP; elim => ab; elim => Hab1 Hab2 He; subst.
  move/allP: H.
  move/(_ _ HC)/allP/(_ _ Hab1)/allP/(_ _ H2)/implyP.
  rewrite He //= in Htr; move/(_ Htr)/allP/(_ _ Hab2)/implyP.
  rewrite He //= in Hneq.
  move/(_ Hneq); rewrite He //=.

  apply/allP => x Hx; apply/allP => a Ha; apply/allP => s Hs; apply/implyP => Htr; apply/allP => b Hb; apply/implyP => Hneq.

  move/allP: H.
  move/(_ ((a,b), s)).
  simpl.
  have: (a,b,s) \in [seq (x0, y) | x0 <- channels_allpairs Cs, y <- fastEnum (pQ P)].
  apply/allpairsP; eexists; split.
  apply/flattenP; eexists.
  apply/mapP; eexists.
  apply Hx.
  apply Logic.eq_refl.
  apply/allpairsP; exists (a,b); split; rewrite //=.
  instantiate (1 := ((a,b), s)); done.
  simpl; done.
  done.
  move => H; move/(_ H).
  move/implyP/(_ Htr)/implyP/(_ Hneq); done.
Qed.

Lemma decide_actionDetermP {A : choiceType} (Cs : seq (seq A)) (P : @prePIOA A) :
  decide_actionDeterm Cs P -> all_fset (actionDeterm P) (channels_of_seqs Cs).
  move/allP => H.
  apply/all_fsetP => x Hx.
  apply/all_fsetP => y Hy.
  apply/forallP => s.
  apply/implyP => Ht.
  apply/all_fsetP => z Hz.
  apply/implyP => Hneq.
  rewrite -in_fset_of_seq in Hx; move/mapP: Hx; elim => X HX1 H'; subst.
  move/allP: (H _ HX1) => H2.
  rewrite -in_fset_of_seq in Hy.
  move/allP: (H2 _ Hy) => H3.
  have: s \in fastEnum (pQ P) by apply mem_fastEnum.
  move => Hs; move/implyP: (H3 _ Hs); move/(_ Ht); move/allP => H4.
  rewrite -in_fset_of_seq in Hz.
  move/implyP: (H4 _ Hz); move/(_ Hneq); done.
Qed.

Check Build_prePIOA.

Definition mkPIOA {A : choiceType} {S : fastEnumType} (st : S)
           (sO sI sH : seq (seq A)) (t : S -> A -> option (Meas S)) :
  let P := Build_prePIOA A S st (channels_of_seqs sO) (channels_of_seqs sI) (channels_of_seqs sH) t in
  fdisj_seq (flatten sI) (flatten sO) ->
  fdisj_seq (flatten sI) (flatten sH) ->
  fdisj_seq (flatten sO) (flatten sH) ->
  channels_pairwise_disj (sI ++ sO ++ sH) ->
  decide_inputenabled (flatten sI) P ->
decide_actionDeterm (sO ++ sH) P ->
all (fun a : A => all (fun s => opt_lift isSubdist (t s a)) (fastEnum S)) (flatten (sI ++ sO ++ sH)) ->
  @PIOA A.
intros; econstructor.
instantiate (1 := P); apply/and4P; split.
apply/and4P; split.
rewrite /inputs /outputs /hiddens //=; apply fdisj_cover_seqP; rewrite //=.
rewrite /inputs /outputs /hiddens //=; apply fdisj_cover_seqP; rewrite //=.
rewrite /inputs /outputs /hiddens //=; apply fdisj_cover_seqP; rewrite //=.
rewrite /channels //= !channels_of_seqs_U.
apply channels_pairwise_disjP.
rewrite -catA //=.
apply decide_inputenabledP; done.
rewrite /lc_channels channels_of_seqs_U; apply decide_actionDetermP; done.
rewrite /actions /inputs /outputs /hiddens !coverU //= !channels_of_seqs_U.
rewrite -all_fset_cover_seq -catA.
move/allP: H5 => Ha.
apply/allP => x Hx.
move/allP: (Ha x Hx) => Ha2.
apply/forallP => s.
apply Ha2.
rewrite mem_fastEnum //=.
Defined.



Ltac tr_isSubdist_multiIf_tac := apply/allP => x Hx; apply/allP => s Hs; apply multiIfP; split_all; rewrite //=; try isSubdist_tac.

Ltac mkPIOA_tac st outs ins hiddens trans :=
  apply (mkPIOA st outs ins hiddens trans);
  [ vm_compute; rewrite //=
  | vm_compute; rewrite //=
  | vm_compute; rewrite //=
  | vm_compute; rewrite //=
  | vm_compute; rewrite //=
  | vm_compute; rewrite //=
  | tr_isSubdist_multiIf_tac ].