From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting Aux FastEnum.


Definition context (C : fastEnumType) := C -> fastEnumType.

Definition consum {C D : fastEnumType} (g1 : context C) (g2 : context D) : context [fastEnumType of (C + D)%type] :=
  fun x =>
    match x with
      | inl a => g1 a
      | inr a => g2 a
                    end.

Notation "G :+: H" := (consum G H) (at level 70).


Definition action {C : fastEnumType} (gamma : context C) := {c : C & gamma c}.
Definition mkact {C : fastEnumType} (gamma : context C) (c : C) (x : gamma c) := existT gamma c x.

Definition decomp_act {C D : fastEnumType} {g1 : context C} {g2 : context D} : action (consum g1 g2) -> (action g1) + (action g2).
  case; case.
  rewrite //= => a g1a; left; apply (mkact g1 a); apply g1a.
  rewrite //= => b g2b; right; apply (mkact g2 b); apply g2b.
Defined.

Definition act_comp {C D : fastEnumType} {g1 : context C} {g2 : context D} : (action g1) + action g2 -> action (consum g1 g2).
  case; case => x gx.
  apply (mkact (consum g1 g2) (inl x)); apply gx.
  apply (mkact (consum g1 g2) (inr x)); apply gx.
Defined.

Lemma act_decomp_cancel {C D : fastEnumType} {g1 : context C} {g2 : context D} :
  cancel (@decomp_act C D g1 g2) (@act_comp C D g1 g2).
  case; case; rewrite //=.
Qed.

Definition action_projL {C D : fastEnumType} (g1 : context C) (g2 : context D) : action (consum g1 g2) -> option (action g1).
  case; case; intros.
  apply (Some (existT _ a p)).
  apply None.
Defined.

Definition action_projR {C D : fastEnumType} (g1 : context C) (g2 : context D) : action (consum g1 g2) -> option (action g2).
  case; case; intros.
  apply None.
  apply (Some (existT _ b p)).
Defined.


Record PIOA {C : fastEnumType} (Gamma : context C) :=
  {
    St : finType;
    start : St;
    inputs : seq C;
    outputs : seq C;
    disj_io : seq_disjoint inputs outputs;
    H : fastEnumType;
    Delta : context H;
    tr : St -> (action Delta + action Gamma) -> option (Meas St);
    ad_h : forall (s : St) (h : H) (m1 m2 : Delta h), tr s (inl (mkact Delta h m1)) != None -> tr s (inl (mkact Delta h m2)) != None -> m1 == m2;
    ad_v : forall (s : St) (c : C) (m1 m2 : Gamma c), tr s (inr (mkact Gamma c m1)) != None -> tr s (inr (mkact Gamma c m2)) != None -> m1 == m2;
    i_a : forall s i, i \in inputs -> forall (m : Gamma i), tr s (inr (mkact Gamma i m)) != None
    }.

Arguments St [C Gamma].
Arguments Delta [C Gamma].
Arguments tr [C Gamma].
Arguments ad_h [C Gamma].
Arguments ad_v [C Gamma].
Arguments H [C Gamma].
Arguments i_a [C Gamma].
Arguments inputs [C Gamma].
Arguments start [C Gamma].
Arguments outputs [C Gamma].


Definition channel {C : fastEnumType} {Gamma : context C} (P : PIOA Gamma) :=
  ((H P) + seq_sub (inputs P ++ outputs P))%type.

Definition enabled {C : fastEnumType} {Gamma : context C} (P : PIOA Gamma) (x : St P) a :=
  tr P x a != None.

Definition trace {C} {Gamma: context C} (P : PIOA Gamma) := seq (action Gamma).

Lemma actDeterm_h {C} {Gamma : context C} (P : PIOA Gamma) (s : St P) (a1 a2 : action (Delta P)) : tag a1 = tag a2 -> tr P s (inl a1) != None -> tr P s (inl a2) != None -> a1 = a2.
  destruct a1; destruct a2; rewrite //=.
  move => Heq; move: s0 s1; rewrite Heq => s0 s1 h1 h2.
  have -> //=: s0 = s1 by apply/eqP; apply (ad_h _ _ _ _ _ h1 h2).
Qed.

Lemma actDeterm_v {C} {Gamma : context C} (P : PIOA Gamma) (s : St P) (a1 a2 : action Gamma) : tag a1 = tag a2 -> tr P s (inr a1) != None -> tr P s (inr a2) != None -> a1 = a2.
  destruct a1; destruct a2; rewrite //=.
  move => Heq; move: s0 s1; rewrite Heq => s0 s1 h1 h2.
  have -> //=: s0 = s1 by apply/eqP; apply (ad_v _ _ _ _ _ h1 h2).
Qed.

Lemma inputEnabled {C} {Gamma : context C} (P : PIOA Gamma) s (a : action Gamma) : tag a \in (inputs P) -> tr P s (inr a) != None.
  by case: a => x p H; apply (i_a P).
Qed.

(* h.x *)
Definition achoose_h {C} {Gamma : context C} (P : PIOA Gamma) (h : (H P)) (x : St P) :=
        omap (fun x => (mkact (Delta P) h x)) (pick (fun (m : Delta P h) => enabled P x (inl (mkact _ h m)))).

(* o.x *)
Definition achoose_v {C} {Gamma : context C} (P : PIOA Gamma) (c : C) (x : St P) :=
        omap (fun x => (mkact Gamma c x)) (pick (fun (m : Gamma c) => enabled P x (inr (mkact _ c m)))).


Definition smap {A B C D} (f : A -> B) (g : C -> D) (x : A + C) : B + D :=
match x with
  | inl a => inl (f a)
  | inr a => inr (g a)
                 end.


Lemma achoose_hP {C} {Gamma : context C} (P : PIOA Gamma) h s a :
  achoose_h P h s = Some a <-> enabled P s (inl a) && (tag a == h).
  split.
  rewrite /achoose_h; case: pickP => [x H | x]; rewrite //= => Heq.
  injection Heq => <-; rewrite //=.
  rewrite H eq_refl //=.
  move/andP => [h1 /eqP h2]; rewrite /achoose_h; case:pickP => [x H | x]; subst. 
  rewrite //=.

  have -> //= : (mkact (Delta P) (tag a) x) = a.
  eapply actDeterm_h.
  done.
  apply H.
  done.

  destruct a; simpl in *; move: x; move/(_ s0); rewrite h1 //=.
Qed.

Lemma achoose_vP {C} {Gamma : context C} (P : PIOA Gamma) h s a :
  achoose_v P h s = Some a <-> enabled P s (inr a) && (tag a == h).
  split.
  rewrite /achoose_v; case: pickP => [x H | x]; rewrite //= => Heq.
  injection Heq => <-; rewrite //=.
  rewrite H eq_refl //=.
  move/andP => [h1 /eqP h2]; rewrite /achoose_v; case:pickP => [x H | x]; subst. 
  rewrite //=.

  have -> //= : (mkact Gamma (tag a) x) = a.
  eapply actDeterm_v.
  done.
  apply H.
  done.

  destruct a; simpl in *; move: x; move/(_ s0); rewrite h1 //=.
Qed.


(* def 3 *)
Definition app_h {C} {Gamma : context C} (P : PIOA Gamma) (h : H P) (s : St P) :=
  oapp (fun ha => oapp id (ret s) (tr P s (inl ha))) (ret s) (achoose_h P h s).

(* the (y) in o.x(y) *)
Definition app_ova {C} {Gamma : context C} (P : PIOA Gamma) (ova : option (action Gamma)) (s : St P) :=
  oapp (fun va => oapp id (ret s) (tr P s (inr va))) (ret s) ova.


Definition ocons {A} (x : option A) (xs : seq A) :=
  match x with | Some a => a :: xs | None => xs end.

(* definition 6 *)
Definition act {C} {Gamma : context C} (P : PIOA Gamma) (hc : (H P) + C) (mu : Meas [choiceType of (St P) * (trace P)]) :=
  match hc with
    | inl h => 
        (xt <- mu; s' <- app_h P h xt.1; ret (s', xt.2))
    | inr c =>
      (*         s' <- o.x(x); ret (s', tau \oplus o.x *)
      (xt <- mu; s' <- app_ova P (achoose_v P c xt.1) xt.1; ret (s', ocons (achoose_v P c xt.1) xt.2))
  end.

Definition locally_controlled {C} {Gamma : context C} (P : PIOA Gamma) (hc : (H P) + C) :=
  match hc with
  | inl _ => true
  | inr c => c \in (outputs P)
                     end.


Definition initDist {C} {Gamma : context C} (P : PIOA Gamma) : Meas [choiceType of (St P) * (trace P)] := ret (start P, nil).

Definition papply {C} {Gamma : context C} (P : PIOA Gamma) (g : seq ((H P) + C)) :=
  foldl (fun acc x => act P x acc) (initDist P) g.

Definition closed {C} {Gamma : context C} (P : PIOA Gamma) := inputs P == nil.













Definition mkPIOA {C} (Gamma : context C) (S : finType) (st : S) (inputs outputs : seq C) (H : fastEnumType) (Delta : context H) (tr : S -> (action Delta + action Gamma) -> option (Meas S)) :
                seq_disjoint inputs outputs ->
                (forall s h m1 m2, tr s (inl (mkact Delta h m1)) != None -> tr s (inl (mkact Delta h m2)) != None -> m1 == m2) ->
                (forall s h m1 m2, tr s (inr (mkact Gamma h m1)) != None -> tr s (inr (mkact Gamma h m2)) != None -> m1 == m2) ->
                (forall s i, i \in inputs -> forall (m : Gamma i), tr s (inr (mkact Gamma i m)) != None) -> PIOA Gamma.
  
Check Build_PIOA.
move => h1 h2 h3 h4.
apply (@Build_PIOA C Gamma S st inputs outputs h1 H Delta tr h2 h3 h4).
Defined.
                                             

Definition extendR {C D} {Gamma : context C} (P : PIOA Gamma) (Gamma' : context D) :
  PIOA (Gamma :+: Gamma').
  apply (mkPIOA _ (St P) (start P) (map inl (inputs P)) (map inl (outputs P)) (H P) (Delta P)
                (fun s a =>
                   match a with
                   | inl h => tr P s (inl h)
                   | inr ab =>
                     match (action_projL Gamma Gamma' ab) with
                     | Some a' => tr P s (inr a')
                     | None => None
                     end
                       end)).

  apply/allP => x Hx. apply/allP => y Hy.
  elim (mapP Hx) => x0 Hx0.
  elim (mapP Hy) => y0 Hy0.
  move => -> => ->.

  destruct P; simpl in *.
  move/allP: disj_io0; move/(_ x0 Hx0)/allP/(_ y0 Hy0) => h; apply/contraT; rewrite negbK //=; move/eqP => Hc; injection Hc => Hc'; rewrite Hc' in h; rewrite eq_refl //= in h; done.
  apply (ad_h P).

  move => s h m1 m2.
  destruct h; rewrite //=.
  apply (ad_v P).

  move => s i Hi m.
  destruct i; rewrite //=.
  apply (i_a P).
  move/mapP: Hi; elim => x0 Hx0 Hc; injection Hc => ->.
  done.

  move/mapP: Hi; elim; done.
Defined.