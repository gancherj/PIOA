(* Actions, contexts, and canonical bijections between action spaces *)


From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Eqdep.

Require Import Meas Lifting Aux FastEnum.

Record ctx := mkCon { cdom : fastEnumType; cfun :> cdom -> fastEnumType }.

Definition consum (c d : ctx)  :=
  mkCon [fastEnumType of ((cdom c) + (cdom d))%type] (fun x => match x with | inl a => c a | inr a => d a end).

Notation "G :+: H" := (consum G H) (at level 70).

Definition conrestr (c : ctx) (s : seq (cdom c)) :=
  mkCon ([fastEnumType of seq_sub s]) (fun x => c (ssval x)).

Notation "G |c_ s" := (conrestr G s) (at level 70).

Definition action (gamma : ctx) := {c : (cdom gamma) & gamma c}.
Definition mkact (gamma : ctx) (c : cdom gamma) (x : gamma c) := existT (cfun gamma) c x.

Record ctxbij (C D : ctx) := Bij { lr : cdom C -> cdom D; rl : cdom D -> cdom C;
                                       lr_can : cancel lr rl;
                                       rl_can : cancel rl lr;
                                       ctx_eq : forall c, C c = D (lr c) }.


Arguments lr [C D].
Arguments rl [C D].
Arguments lr_can [C D].
Arguments rl_can [C D].
Arguments ctx_eq [C D].

Notation "C ~~ D" := (ctxbij C D) (at level 70).


Definition ctx_symm {C D : ctx} (H : C ~~ D) : D ~~ C.
  apply (Bij D C (rl H) (lr H)).
  by elim H.
  by elim H.
  elim H => f g fg gf ctx c; simpl in *.
  rewrite ctx.
  rewrite gf; done.
Defined.

Definition bij_msg {C D : ctx} (H : C ~~ D) {c : cdom C} (a : C c) : D (lr H c).
rewrite -(ctx_eq H).
apply a.
Defined.

Lemma bijmsg_inj {C D : ctx} (H : C ~~ D) (c : cdom C) : injective (fun a : C c => bij_msg H a).
  move => x y.
  rewrite /bij_msg //=.
  rewrite /eq_rect //=.
  case (ctx_eq H c); done.
Qed.

Notation "H *m m" := (bij_msg H m) (at level 70).
Notation "H *c m" := (lr H m) (at level 70).

Definition bijaction {C D : ctx} (H : C ~~ D) (a : action C) : action D :=
  mkact D (H *c (tag a)) (H *m (projT2 a)).

Lemma bijaction_inj {C D : ctx} (H : C ~~ D) :
  injective (bijaction H).
  case => c1 m1; case => c2 m2.
  rewrite /bijaction //= /mkact => Heq.
  apply eq_sigT_eq_dep in Heq.
  inversion Heq.
  have heqc: c1 = c2.
  have: injective (lr H).
  apply bij_inj; apply (Bijective (lr_can H) (rl_can H)).
  move/(_ _ _ H1); done.
  clear Heq H1 H2.
  move : m1 m2 H3.
  rewrite heqc; clear heqc => m1 m2 h.
  have heqhm : (H *m m1) = (H *m m2).
  apply (inj_pair2 _ (fun x : cdom D => D x)); done.
  
  move: (bijmsg_inj H c2).
  move/(_ _ _ heqhm) => heqm.
  move: heqm; clear => ->; done.
Qed.

Notation "H *a a" := (bijaction H a) (at level 70).

Lemma bijactionE (C D : ctx) (H : ctxbij C D) (c : cdom C) (m : C c) :
  H *a (mkact C c m) =
  mkact D (H *c c) (H *m m).
  rewrite /bijaction //=.
Qed.

Inductive void : Set := .

Definition void_to_unit (x : void) : unit :=
  match x with end.

Definition unit_to_void (x : unit) : option void := None.

Lemma void_pcancel : pcancel void_to_unit unit_to_void.
  case.
Qed.

Canonical void_eqtype := EqType void (PcanEqMixin void_pcancel).
Canonical void_choice := ChoiceType void (PcanChoiceMixin void_pcancel).
Canonical void_count := CountType void (PcanCountMixin void_pcancel).
Canonical void_fin := FinType void (PcanFinMixin void_pcancel).
Lemma void_fe : FastEnum.axiom _ (nil : seq void).
  apply uniq_perm_eq.
  done.
  apply enum_uniq.
  case.
Qed.
Canonical void_fetype := FastEnumType void (FastEnumMixin _ _ void_fe).

Definition emptyCtx :=
  mkCon [fastEnumType of void] (fun x => match x with end).

Definition empty_plus_r (C : ctx) :  C ~~ (C :+: emptyCtx).
  apply (Bij C (C :+: emptyCtx) inl (fun x => match x with |inl a => a | inr r => match r with end end)).
  done.
  case; done.
  done.
Defined.

Definition empty_plus_l (C : ctx) :  C ~~ (emptyCtx :+: C).
  apply (Bij C (emptyCtx :+: C) inr (fun x => match x with |inl v => match v with end | inr a => a end)).
  done.
  by case.
  done.
Defined.
