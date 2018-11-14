From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting Aux FastEnum.

Record context := mkCon { cdom : finType; cfun :> cdom -> finType }.


Definition consum (c d : context) :=
  mkCon [finType of ((cdom c) + (cdom d))%type] (fun x => match x with | inl a => c a | inr a => d a end).

Notation "G :+: H" := (consum G H) (at level 70).


Definition action (gamma : context) := {c : (cdom gamma) & gamma c}.
Definition mkact (gamma : context) (c : cdom gamma) (x : gamma c) := existT (cfun gamma) c x.

Definition decomp_act {g1 : context} {g2 : context} : action (g1 :+: g2) -> (action g1) + (action g2).
  case; case.
  rewrite //= => a g1a; left; apply (mkact g1 a); apply g1a.
  rewrite //= => b g2b; right; apply (mkact g2 b); apply g2b.
Defined.

Definition act_comp {g1 : context} {g2 : context} : (action g1) + action g2 -> action (g1 :+: g2).
  case; case => x gx.
  apply (mkact (consum g1 g2) (inl x)); apply gx.
  apply (mkact (consum g1 g2) (inr x)); apply gx.
Defined.

Lemma act_decomp_cancel {g1 : context} {g2 : context} :
  cancel (@decomp_act g1 g2) (@act_comp g1 g2).
  case; case; rewrite //=.
Qed.

Record PIOA (Gamma : context) (Delta : context) :=
  {
    St : finType;
    start : St;
    inputs : seq (cdom Gamma);
    outputs : seq (cdom Gamma);
    disj_io : seq_disjoint inputs outputs;
    tr : St -> (action Delta + action Gamma) -> option ({meas St});
    ad_h : forall (s : St) (h : cdom Delta) (m1 m2 : Delta h), tr s (inl (mkact Delta h m1)) != None -> tr s (inl (mkact Delta h m2)) != None -> m1 == m2;
    ad_v : forall (s : St) (c : cdom Gamma) (m1 m2 : Gamma c), tr s (inr (mkact Gamma c m1)) != None -> tr s (inr (mkact Gamma c m2)) != None -> m1 == m2;
    i_a : forall s i, i \in inputs -> forall (m : Gamma i), tr s (inr (mkact Gamma i m)) != None
    }.

Arguments St [Gamma Delta].
Arguments tr [Gamma Delta].
Arguments ad_h [Gamma Delta].
Arguments ad_v [Gamma Delta].
Arguments i_a [Gamma Delta].
Arguments inputs [Gamma Delta].
Arguments start [Gamma Delta].
Arguments outputs [Gamma Delta].

Definition C {G D : context} (P : PIOA G D) := cdom G.
Definition H {G D : context} (P : PIOA G D) := cdom D.

Definition channel {G D : context} (P : PIOA G D) :=
  ((H P) + seq_sub (inputs P ++ outputs P))%type.

Definition enabled  {G D : context} (P : PIOA G D) (x : St P) a :=
  tr P x a != None.

Definition trace {G D : context} (P : PIOA G D) := seq (action G).

Lemma actDeterm_h {G D : context} (P : PIOA G D) (s : St P) (a1 a2 : action D) : tag a1 = tag a2 -> tr P s (inl a1) != None -> tr P s (inl a2) != None -> a1 = a2.
  destruct a1; destruct a2; rewrite //=.
  move => Heq; move: s0 s1; rewrite Heq => s0 s1 h1 h2.
  have -> //=: s0 = s1 by apply/eqP; apply (ad_h _ _ _ _ _ h1 h2).
Qed.

Lemma actDeterm_v {G D : context} (P : PIOA G D) (s : St P) (a1 a2 : action G) : tag a1 = tag a2 -> tr P s (inr a1) != None -> tr P s (inr a2) != None -> a1 = a2.
  destruct a1; destruct a2; rewrite //=.
  move => Heq; move: s0 s1; rewrite Heq => s0 s1 h1 h2.
  have -> //=: s0 = s1 by apply/eqP; apply (ad_v _ _ _ _ _ h1 h2).
Qed.

Lemma inputEnabled  {G D : context} (P : PIOA G D) s (a : action G) : tag a \in (inputs P) -> tr P s (inr a) != None.
  by case: a => x p H; apply (i_a P).
Qed.

(* h.x *)
Definition achoose_h {G D : context} (P : PIOA G D) (h : (H P)) (x : St P) :=
        omap (fun x => (mkact D h x)) (pick (fun (m : D h) => enabled P x (inl (mkact _ h m)))).

(* o.x *)
Definition achoose_v {G D : context} (P : PIOA G D) (c : C P) (x : St P) :=
        omap (fun x => (mkact G c x)) (pick (fun (m : G c) => enabled P x (inr (mkact _ c m)))).


Definition smap {A B C D} (f : A -> B) (g : C -> D) (x : A + C) : B + D :=
match x with
  | inl a => inl (f a)
  | inr a => inr (g a)
                 end.


Lemma achoose_hP {G D : context} (P : PIOA G D) h s a :
  achoose_h P h s = Some a <-> enabled P s (inl a) && (tag a == h).
  split.
  rewrite /achoose_h; case: pickP => [x H | x]; rewrite //= => Heq.
  injection Heq => <-; rewrite //=.
  rewrite H eq_refl //=.
  move/andP => [h1 /eqP h2]; rewrite /achoose_h; case:pickP => [x H | x]; subst. 
  rewrite //=.

  have -> //= : (mkact (D) (tag a) x) = a.
  eapply actDeterm_h.
  done.
  apply H.
  done.

  destruct a; simpl in *; move: x; move/(_ s0); rewrite h1 //=.
Qed.

Lemma achoose_vP {G D : context} (P : PIOA G D) h s a :
  achoose_v P h s = Some a <-> enabled P s (inr a) && (tag a == h).
  split.
  rewrite /achoose_v; case: pickP => [x H | x]; rewrite //= => Heq.
  injection Heq => <-; rewrite //=.
  rewrite H eq_refl //=.
  move/andP => [h1 /eqP h2]; rewrite /achoose_v; case:pickP => [x H | x]; subst. 
  rewrite //=.

  have -> //= : (mkact G (tag a) x) = a.
  eapply actDeterm_v.
  done.
  apply H.
  done.

  destruct a; simpl in *; move: x; move/(_ s0); rewrite h1 //=.
Qed.


(* def 3 *)
Definition app_h {G D : context} (P : PIOA G D) (h : H P) (s : St P) :=
  oapp (fun ha => oapp id (ret s) (tr P s (inl ha))) (ret s) (achoose_h P h s).

(* the (y) in o.x(y) *)
Definition app_ova  {G D : context} (P : PIOA G D) (ova : option (action G)) (s : St P) :=
  oapp (fun va => oapp id (ret s) (tr P s (inr va))) (ret s) ova.


Definition ocons {A} (x : option A) (xs : seq A) :=
  match x with | Some a => a :: xs | None => xs end.

(* definition 6 *)
Definition act {G D : context} (P : PIOA G D) (hc : (H P) + (C P)) (mu : {meas (St P) * (trace P)}) :=
  match hc with
    | inl h => 
        (xt <- mu; s' <- app_h P h xt.1; ret (s', xt.2))
    | inr c =>
      (*         s' <- o.x(x); ret (s', tau \oplus o.x *)
      (xt <- mu; s' <- app_ova P (achoose_v P c xt.1) xt.1; ret (s', ocons (achoose_v P c xt.1) xt.2))
  end.

Definition locally_controlled  {G D : context} (P : PIOA G D) (hc : (H P) + (C P)) :=
  match hc with
  | inl _ => true
  | inr c => c \in (outputs P)
                     end.


Definition initDist {G D : context} (P : PIOA G D) : {meas (St P) * (trace P)} := ret (start P, nil).

Definition run {G D : context} (P : PIOA G D) (g : seq ((H P) + (C P))) :=
  foldl (fun acc x => act P x acc) (initDist P) g.

Definition closed {G D : context} (P : PIOA G D) := inputs P == nil.

Definition apply_i {G D : context} (P : PIOA G D) (a : action G) (mu : {meas (St P) * (trace P)}) :=
  (xt <- mu; s' <- app_ova P (Some a) xt.1; ret (s', a :: xt.2)).

Lemma run_rcons {G D : context} (P : PIOA G D) xs x :
  run P (rcons xs x) = act P x (run P xs).
  rewrite /run //=.
  rewrite -cats1 foldl_cat //=.
Qed.

Lemma act_bind {G D : context} {A : choiceType} (P : PIOA G D) a (m : Meas A) f :
  act P a (measBind m f) = measBind m (fun x => act P a (f x)).
  rewrite /act; case a => x; by rewrite bindAssoc.
Qed.



Definition mkPIOA (G : context) (S : finType) (st : S) (inputs outputs : seq (cdom G)) (Delta : context) (tr : S -> (action Delta + action G) -> option ({meas S})) :
                seq_disjoint inputs outputs ->
                (forall s h m1 m2, tr s (inl (mkact Delta h m1)) != None -> tr s (inl (mkact Delta h m2)) != None -> m1 == m2) ->
                (forall s h m1 m2, tr s (inr (mkact G h m1)) != None -> tr s (inr (mkact G h m2)) != None -> m1 == m2) ->
                (forall s i, i \in inputs -> forall (m : G i), tr s (inr (mkact G i m)) != None) -> PIOA G Delta.
  
move => h1 h2 h3 h4.
apply (@Build_PIOA G Delta S st inputs outputs h1 tr h2 h3 h4).
Defined.
                                             

(* TODO : move proof to Qed lemma *)
Definition extendG {G D : context} (P : PIOA G D) (G' : context) :
  PIOA (G :+: G') D.
  Check decomp_act.
  apply (mkPIOA (G :+: G') (St P) (start P) (map inl (inputs P)) (map inl (outputs P)) D 
                (fun s a =>
                   match a with
                   | inl h => tr P s (inl h)
                   | inr ab =>
                     match (decomp_act ab) with
                     | inl a' => tr P s (inr a')
                     | _ => None
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

