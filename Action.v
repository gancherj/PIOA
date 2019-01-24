(* Actions, contexts, and canonical bijections between action spaces *)

(* Need a good standard library of operations so that no dependent equality needs to show up in higher level proofs. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Eqdep.

Require Import Meas Closure Aux FastEnum.

Record ctx := mkCon { cdom : choiceType; cfun :> cdom -> finType }.

Definition consum (c d : ctx)  :=
  mkCon [choiceType of ((cdom c) + (cdom d))%type] (fun x => match x with | inl a => c a | inr a => d a end).

Notation "G :+: H" := (consum G H) (at level 70).

Definition conrestr (c : ctx) (s : seq (cdom c)) :=
  mkCon ([finType of seq_sub s]) (fun x => c (ssval x)).

Notation "G |c_ s" := (conrestr G s) (at level 70).

Definition action (gamma : ctx) := {c : (cdom gamma) & gamma c}.
Definition mkact (gamma : ctx) (c : cdom gamma) (x : gamma c) := existT (cfun gamma) c x.

(* TODO: separate proofs into opaque part *)
Record ctxbij_spec (C D : ctx) (lr : cdom C -> cdom D) (rl : cdom D -> cdom C) :=
  {
    lr_can : cancel lr rl;
    rl_can : cancel rl lr;
    ctx_eq : forall c, C c = D (lr c)
                               }.

Record ctxbij (C D : ctx) := Bij { lr : cdom C -> cdom D; rl : cdom D -> cdom C;
                                   bij_spec :> ctxbij_spec C D lr rl}.


Arguments lr [C D].
Arguments rl [C D].
Arguments lr_can [C D lr rl].
Arguments rl_can [C D lr rl].
Arguments ctx_eq [C D lr rl].
Arguments bij_spec [C D].

Notation "C ~~ D" := (ctxbij C D) (at level 70).


Lemma ctx_symm_spec {C D : ctx} (H : C ~~ D) : ctxbij_spec D C (rl H) (lr H).
  constructor.
  elim H => lr rl; case; done.
  elim H => lr rl; case; done.
  elim H => lr rl; case; intros; simpl; rewrite ctx_eq0 rl_can0; done.
Qed.

Definition ctx_symm {C D : ctx} (H : C ~~ D) : D ~~ C.
 apply (Bij D C (rl H) (lr H)).
 apply ctx_symm_spec.
Defined.

Definition bij_msg {C D : ctx} (H : C ~~ D) {c : cdom C} (a : C c) : D (lr H c).
rewrite -(ctx_eq H); done.
Defined.

Definition bij_msg_inv {C D : ctx} (H : C ~~ D) {c : cdom C} (a : D (lr H c)) : C c.
  rewrite (ctx_eq H).
  apply a.
Defined.

Lemma bij_msg_invP {C D : ctx} (H : C ~~ D) {c : cdom C} (a : D (lr H c)) :
  bij_msg H (bij_msg_inv H a) = a.
  rewrite /bij_msg /bij_msg_inv //=.
  rewrite rew_opp_r //=.
Qed.

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

  Lemma msg_inv {C D : ctx} (H : C ~~ D) :
   forall h x, exists m,
          (mkact D (H *c h) x) = (H *a mkact C h m).
    move => h x.
    exists (bij_msg_inv _ x).
    rewrite bijactionE.
    rewrite bij_msg_invP //=.
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

Instance fevoid : FastEnum [finType of void] :=
  {fastEnum := [::]}.
  apply uniq_perm_eq.
  done.
  apply enum_uniq.
  case.
Defined.

Definition emptyCtx :=
  mkCon [finType of void] (fun x => match x with end).

Check ctxbij_spec.
Lemma empty_plus_r_spec (C : ctx) : ctxbij_spec C (C :+: emptyCtx) inl  (fun x => match x with |inl a => a | inr r => match r with end end).
  constructor.
  done.
  case; done.
  done.
Qed.

Definition empty_plus_r (C : ctx) : C ~~ (C :+: emptyCtx).
 econstructor.
 apply empty_plus_r_spec.
Defined.

Lemma empty_plus_l_spec (C : ctx) : ctxbij_spec C (emptyCtx :+: C) inr  (fun x => match x with |inr a => a | inl r => match r with end end).
  constructor.
  done.
  case; done.
  done.
Qed.

Definition empty_plus_l (C : ctx) : C ~~ (emptyCtx :+: C).
 econstructor.
 apply empty_plus_l_spec.
Defined.

Definition ctx_plus_symm_spec (C D : ctx) : ctxbij_spec (C :+: D) (D :+: C) 
             (fun p => match p with | inl a => inr a | inr a => inl a end)
             (fun p => match p with | inl a => inr a | inr a => inl a end).
  constructor; by case.
Qed.
Definition ctx_plus_symm (C D : ctx) : (C :+: D) ~~ (D :+: C) .
    econstructor.
    apply ctx_plus_symm_spec.
Defined.

Lemma ctx_plus_assoc_spec (C D E : ctx) :
  ctxbij_spec (C :+: (D :+: E)) ((C :+: D) :+: E)
             (fun p => match p with | inl c => inl (inl c) | inr (inl d) => inl (inr d) | inr (inr e) => inr e end)
             (fun p => match p with | inl (inl c) => inl c | inl (inr d) => inr (inl d) | inr e => inr (inr e) end).
  constructor.
  case; [done | by case].
  case; [by case | done].
  case; [done | by case].
Qed.

Definition ctx_plus_assoc (C D E : ctx) : (C :+: (D :+: E)) ~~ ((C :+: D) :+: E).
  econstructor; apply ctx_plus_assoc_spec.
Defined.