

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting Aux FastEnum Action .

Record PIOA_data (Gamma : ctx) (Delta : ctx) :=
  {
    St : finType;
    start : St;
    inputs : seq (cdom Gamma);
    outputs : seq (cdom Gamma);
    tr : St -> (action Delta + action Gamma) -> option {meas St}
                                                       }.

Arguments St [Gamma Delta].
Arguments tr [Gamma Delta].
Arguments inputs [Gamma Delta].
Arguments start [Gamma Delta].
Arguments outputs [Gamma Delta].

Record PIOA_spec {Gamma Delta : ctx} (d : PIOA_data Gamma Delta) :=
  {
    disj_io : seq_disjoint (inputs d) (outputs d);
    ad_h : forall (s : St d) (h : cdom Delta) (m1 m2 : Delta h), tr d s (inl (mkact Delta h m1)) != None -> tr d s (inl (mkact Delta h m2)) != None -> m1 == m2;
    ad_v : forall (s : St d) (c : cdom Gamma) (m1 m2 : Gamma c), (c \in outputs d) -> tr d s (inr (mkact Gamma c m1)) != None -> tr d s (inr (mkact Gamma c m2)) != None -> m1 == m2;
    i_a : forall s i, i \in inputs d -> forall (m : Gamma i), tr d s (inr (mkact Gamma i m)) != None
                                                               }.

Record PIOA (Gamma : ctx) (Delta : ctx) :=
  {
    pdata :> PIOA_data Gamma Delta;
    _ : PIOA_spec pdata
    }.


Arguments disj_io [Gamma Delta d].
Arguments ad_h [Gamma Delta d].
Arguments ad_v [Gamma Delta d].
Arguments i_a [Gamma Delta d].

Definition C {G D : ctx} (P : PIOA G D) := cdom G.
Definition H {G D : ctx} (P : PIOA G D) := cdom D.

Definition channel {G D : ctx} (P : PIOA G D) :=
  ((H P) + seq_sub (inputs P ++ outputs P))%type.

Definition enabled  {G D : ctx} (P : PIOA G D) (x : St P) a :=
  tr P x a != None.

Definition trace {G D : ctx} (P : PIOA G D) := seq (action G).

Lemma PIOAP {Gamma Delta : ctx} (P : PIOA Gamma Delta) : PIOA_spec P.
  destruct P; done.
Qed.

Lemma actDeterm_h {G D : ctx} (P : PIOA G D) (s : St P) (a1 a2 : action D) : tag a1 = tag a2 -> tr P s (inl a1) != None -> tr P s (inl a2) != None -> a1 = a2.
  destruct a1; destruct a2; rewrite //=.
  move => Heq; move: s0 s1; rewrite Heq => s0 s1 h1 h2.
  have -> //=: s0 = s1.
  apply /eqP; apply (ad_h (PIOAP P) s); done.
Qed.

Lemma actDeterm_v {G D : ctx} (P : PIOA G D) (s : St P) (a1 a2 : action G) : tag a1 \in outputs P -> tag a1 = tag a2 -> tr P s (inr a1) != None -> tr P s (inr a2) != None -> a1 = a2.
  destruct a1; destruct a2; rewrite //=.
  move => Hx Heq; move: s0 s1; rewrite Heq => s0 s1 h1 h2.
  subst.
  have -> //= : s0 = s1.
  apply/eqP; apply (ad_v (PIOAP P) s); done.
Qed.

Lemma inputEnabled  {G D : ctx} (P : PIOA G D) s (a : action G) : tag a \in (inputs P) -> tr P s (inr a) != None.
  by case: a => x p H; apply (i_a (PIOAP P)).
Qed.

(* h.x *)
Definition pick_h {G D : ctx} (P : PIOA G D) (h : (H P)) (x : St P) :=
        omap (fun x => (mkact D h x)) (pick (fun (m : D h) => enabled P x (inl (mkact _ h m)))).

(* o.x *)
Definition pick_v {G D : ctx} (P : PIOA G D) (c : C P) (x : St P) :=
        omap (fun x => (mkact G c x)) (pick (fun (m : G c) => enabled P x (inr (mkact _ c m)))).

Lemma pick_hP {G D : ctx} (P : PIOA G D) h s a :
  pick_h P h s = Some a <-> enabled P s (inl a) && (tag a == h).
  split.
  rewrite /pick_h; case: pickP => [x H | x]; rewrite //= => Heq.
  injection Heq => <-; rewrite //=.
  rewrite H eq_refl //=.
  move/andP => [h1 /eqP h2]; rewrite /pick_h; case:pickP => [x H | x]; subst. 
  rewrite //=.

  have -> //= : (mkact (D) (tag a) x) = a.
  eapply actDeterm_h.
  done.
  apply H.
  done.

  destruct a; simpl in *; move: x; move/(_ s0); rewrite h1 //=.
Qed.

Lemma pick_vP {G D : ctx} (P : PIOA G D) h s a : h \in outputs P ->
  pick_v P h s = Some a <-> enabled P s (inr a) && (tag a == h).
  move => Hh.
  split.
  rewrite /pick_v; case: pickP => [x H | x]; rewrite //= => Heq.
  injection Heq => <-; rewrite //=.
  rewrite H eq_refl //=.
  move/andP => [h1 /eqP h2]; rewrite /pick_v; case:pickP => [x H | x]; subst. 
  rewrite //=.


  have -> //= : (mkact G (tag a) x) = a.
  eapply actDeterm_v.
  simpl.
  apply Hh.
  done.
  apply H.
  done.

  destruct a; simpl in *; move: x; move/(_ s0); rewrite h1 //=.
Qed.


(* def 3 *)
Definition app_h {G D : ctx} (P : PIOA G D) (h : H P) (s : St P) : {meas St P} :=
  match (pick_h P h s) with
  | None => ret s
  | Some ha =>
    match (tr P s (inl ha)) with
    | None => ret s
    | Some mu => mu
    end
      end.

Definition app_v {G D : ctx} (P : PIOA G D) (v : C P) (s : St P) : {meas (St P) * option (action G)} :=
  match (pick_v P v s) with
  | None => ret (s, None)
  | Some va =>
    match (tr P s (inr va)) with
    | None => ret (s, None)
    | Some mu => (x <- mu; ret (x, Some va))
    end
      end.

Definition app_i {G D : ctx} (P : PIOA G D) (a : action G) (s : St P) :=
  match (tr P s (inr a)) with
  | None => ret s
  | Some mu => mu
                 end.

Definition ocons {A} (x : option A) (xs : seq A) :=
  match x with | Some a => a :: xs | None => xs end.

Definition act {G D : ctx} (P : PIOA G D) (hc : (H P) + (C P)) (mu : {meas (St P) * (trace P)}) :=
  match hc with
    | inl h =>
      (xt <- mu; s' <- app_h P h xt.1; ret (s', xt.2))
    | inr v =>
      (xt <- mu; p <- app_v P v xt.1; ret (p.1, ocons p.2 xt.2))
        end.

Definition locally_controlled  {G D : ctx} (P : PIOA G D) (hc : (H P) + (C P)) :=
  match hc with
  | inl _ => true
  | inr c => c \in (outputs P)
                     end.


Definition initDist {G D : ctx} (P : PIOA G D) : {meas (St P) * (trace P)} := ret (start P, nil).

Definition run {G D : ctx} (P : PIOA G D) (g : seq ((H P) + (C P))) :=
  foldl (fun acc x => act P x acc) (initDist P) g.

Definition closed {G D : ctx} (P : PIOA G D) := inputs P == nil.


(* TODO: this is redundant *)
Definition apply_i {G D : ctx} (P : PIOA G D) (a : action G) (mu : {meas (St P) * (trace P)}) :=
  (xt <- mu;
     match (tr P xt.1 (inr a)) with
     | None => ret xt
     | Some mu' => s' <- mu'; ret (s', a :: xt.2)
                                  end).
                   

Lemma run_rcons {G D : ctx} (P : PIOA G D) xs x :
  run P (rcons xs x) = act P x (run P xs).
  rewrite /run //=.
  rewrite -cats1 foldl_cat //=.
Qed.

Lemma act_bind {G D : ctx} {A : choiceType} (P : PIOA G D) a (m : {meas A}) f :
  act P a (x <- m; f x) = (x <- m; act P a (f x)).
  rewrite /act; case a => x; by rewrite mbindA.
Qed.

Definition mkPIOA (G D : ctx) (d : PIOA_data G D):
  PIOA_spec d  -> PIOA G D :=
  fun h =>
(Build_PIOA G D d h).
                                             

(* TODO : move proof to Qed lemma *)
(*
Definition extendG {G D : ctx} (P : PIOA G D) (G' : ctx) :
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
*)



(* TODO fix
Ltac mkPIOA_tac g d st ins outs t :=
  apply (mkPIOA g _ st ins outs d t); [
    by vm_compute | apply/decide_ad_hP; by vm_compute | apply/decide_ad_vP; by vm_compute | apply/ decide_i_aP; by vm_compute ].
*)


