From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting Aux FastEnum Action.


Record PIOA (Gamma : ctx) (Delta : ctx) :=
  {
    St : choiceType;
    start : St;
    inputs : seq (cdom Gamma);
    outputs : seq (cdom Gamma);
    disj_io : seq_disjoint inputs outputs;
    tr : St -> (action Delta + action Gamma) -> option ({meas St});
    ad_h : forall (s : St) (h : cdom Delta) (m1 m2 : Delta h), tr s (inl (mkact Delta h m1)) != None -> tr s (inl (mkact Delta h m2)) != None -> m1 == m2;
    ad_v : forall (s : St) (c : cdom Gamma) (m1 m2 : Gamma c), (c \in outputs) -> tr s (inr (mkact Gamma c m1)) != None -> tr s (inr (mkact Gamma c m2)) != None -> m1 == m2;
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

Definition C {G D : ctx} (P : PIOA G D) := cdom G.
Definition H {G D : ctx} (P : PIOA G D) := cdom D.

Definition channel {G D : ctx} (P : PIOA G D) :=
  ((H P) + seq_sub (inputs P ++ outputs P))%type.

Definition enabled  {G D : ctx} (P : PIOA G D) (x : St P) a :=
  tr P x a != None.

Definition trace {G D : ctx} (P : PIOA G D) := seq (action G).

Lemma actDeterm_h {G D : ctx} (P : PIOA G D) (s : St P) (a1 a2 : action D) : tag a1 = tag a2 -> tr P s (inl a1) != None -> tr P s (inl a2) != None -> a1 = a2.
  destruct a1; destruct a2; rewrite //=.
  move => Heq; move: s0 s1; rewrite Heq => s0 s1 h1 h2.
  have -> //=: s0 = s1 by apply/eqP; apply (ad_h _ _ _ _ _ h1 h2).
Qed.

Lemma actDeterm_v {G D : ctx} (P : PIOA G D) (s : St P) (a1 a2 : action G) : tag a1 \in outputs P -> tag a1 = tag a2 -> tr P s (inr a1) != None -> tr P s (inr a2) != None -> a1 = a2.
  destruct a1; destruct a2; rewrite //=.
  move => Hx Heq; move: s0 s1; rewrite Heq => s0 s1 h1 h2.
  rewrite Heq in Hx.
  have -> //=: s0 = s1 by apply/eqP; apply (ad_v _ _ _ _ _ Hx h1 h2).
Qed.

Lemma inputEnabled  {G D : ctx} (P : PIOA G D) s (a : action G) : tag a \in (inputs P) -> tr P s (inr a) != None.
  by case: a => x p H; apply (i_a P).
Qed.

(* h.x *)
Definition achoose_h {G D : ctx} (P : PIOA G D) (h : (H P)) (x : St P) :=
        omap (fun x => (mkact D h x)) (pick (fun (m : D h) => enabled P x (inl (mkact _ h m)))).

(* o.x *)
Definition achoose_v {G D : ctx} (P : PIOA G D) (c : C P) (x : St P) :=
        omap (fun x => (mkact G c x)) (pick (fun (m : G c) => enabled P x (inr (mkact _ c m)))).

Lemma achoose_hP {G D : ctx} (P : PIOA G D) h s a :
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

Lemma achoose_vP {G D : ctx} (P : PIOA G D) h s a : h \in outputs P ->
  achoose_v P h s = Some a <-> enabled P s (inr a) && (tag a == h).
  move => Hh.
  split.
  rewrite /achoose_v; case: pickP => [x H | x]; rewrite //= => Heq.
  injection Heq => <-; rewrite //=.
  rewrite H eq_refl //=.
  move/andP => [h1 /eqP h2]; rewrite /achoose_v; case:pickP => [x H | x]; subst. 
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
Definition app_h {G D : ctx} (P : PIOA G D) (h : H P) (s : St P) :=
  oapp (fun ha => oapp id (ret s) (tr P s (inl ha))) (ret s) (achoose_h P h s).

(* the (y) in o.x(y) *)
Definition app_ova  {G D : ctx} (P : PIOA G D) (ova : option (action G)) (s : St P) :=
  oapp (fun va => oapp id (ret s) (tr P s (inr va))) (ret s) ova.


Definition ocons {A} (x : option A) (xs : seq A) :=
  match x with | Some a => a :: xs | None => xs end.

(* definition 6 *)
Definition act {G D : ctx} (P : PIOA G D) (hc : (H P) + (C P)) (mu : {meas (St P) * (trace P)}) :=
  match hc with
    | inl h => 
        (xt <- mu; s' <- app_h P h xt.1; ret (s', xt.2))
    | inr c =>
      (*         s' <- o.x(x); ret (s', tau \oplus o.x *)
      (xt <- mu; s' <- app_ova P (achoose_v P c xt.1) xt.1; ret (s', ocons (achoose_v P c xt.1) xt.2))
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

Definition apply_i {G D : ctx} (P : PIOA G D) (a : action G) (mu : {meas (St P) * (trace P)}) :=
  (xt <- mu; s' <- app_ova P (Some a) xt.1; ret (s', a :: xt.2)).

Lemma run_rcons {G D : ctx} (P : PIOA G D) xs x :
  run P (rcons xs x) = act P x (run P xs).
  rewrite /run //=.
  rewrite -cats1 foldl_cat //=.
Qed.

Lemma act_bind {G D : ctx} {A : choiceType} (P : PIOA G D) a (m : Meas A) f :
  act P a (x <- m; f x) = (x <- m; act P a (f x)).
  rewrite /act; case a => x; by rewrite mbindA.
Qed.



Definition mkPIOA (G : ctx) (S : choiceType) (st : S) (inputs outputs : seq (cdom G)) (Delta : ctx) (tr : S -> (action Delta + action G) -> option ({meas S})) :
                seq_disjoint inputs outputs ->
                (forall s h m1 m2, tr s (inl (mkact Delta h m1)) != None -> tr s (inl (mkact Delta h m2)) != None -> m1 == m2) ->
                (forall s h m1 m2, h \in outputs -> tr s (inr (mkact G h m1)) != None -> tr s (inr (mkact G h m2)) != None -> m1 == m2) ->
                (forall s i, i \in inputs -> forall (m : G i), tr s (inr (mkact G i m)) != None) -> PIOA G Delta.
  
move => h1 h2 h3 h4.
apply (@Build_PIOA G Delta S st inputs outputs h1 tr h2 h3 h4).
Defined.
                                             

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

Section Reflections.
  Context (Gamma Delta : ctx) (S : fastEnumType) (t : S -> (action Delta) + (action Gamma) -> option {meas S}) (inputs outputs : seq (cdom Gamma)) . 
  Definition decide_ad_h :=
    fall (S) (fun s => fall (cdom Delta) (fun h => fall (Delta h) (fun m1 => fall (Delta h) (fun m2 => (t s (inl (mkact Delta h m1)) != None) ==> (t s (inl (mkact Delta h m2)) != None) ==> (m1 == m2))))). 

  Definition decide_ad_v :=
    fall (S ) (fun s => all (fun h => fall (Gamma h) (fun m1 => fall (Gamma h) (fun m2 => (t s (inr (mkact Gamma h m1)) != None) ==> (t  s (inr (mkact Gamma h m2)) != None) ==> (m1 == m2)))) (outputs)).

  Definition decide_i_a :=
    fall (S) (fun s => all (fun i => fall (Gamma i) (fun m => t s (inr (mkact Gamma i m)) != None)) (inputs)).

  Lemma decide_ad_hP :
    reflect (forall (s : S) (h : cdom Delta) (m1 m2 : Delta h), t s (inl (mkact Delta h m1)) != None -> t s (inl (mkact Delta h m2)) != None -> m1 == m2) (decide_ad_h).
    apply/(iffP idP); rewrite /decide_ad_h.

    move => H s h m1 m2.
    move/fallP: H; move/(_ s)/fallP/(_ h)/fallP/(_ m1)/fallP/(_ m2)/implyP => h1 h2.
    move/implyP: (h1 h2); done.

    move => H.
    apply/fallP => s; apply/fallP => h; apply/fallP => m1; apply/fallP => m2; apply/implyP => h2; apply/implyP.
    apply H; done.
  Qed.


  Lemma decide_ad_vP :
    reflect (forall (s : S) (h : cdom Gamma) (m1 m2 : Gamma h), h \in outputs -> t s (inr (mkact Gamma h m1)) != None -> t s (inr (mkact Gamma h m2)) != None -> m1 == m2) (decide_ad_v).
    apply/(iffP idP); rewrite /decide_ad_h.


    move => H s h m1 m2 Hh.
    move/fallP: H; move/(_ s)/allP/(_ _ Hh)/fallP/(_ m1)/fallP/(_ m2)/implyP => h1 h2.

    move/implyP: (h1 h2); done.

    move => H.
    apply/fallP => s; apply/allP => h Hh; apply/fallP => m1; apply/fallP => m2; apply/implyP => h2; apply/implyP.
    apply H; done.
  Qed.

  Lemma decide_i_aP :
    reflect (forall s i, i \in inputs -> forall (m : Gamma i), t s (inr (mkact Gamma i m)) != None) (decide_i_a).
    apply/(iffP idP); rewrite /decide_i_a.
    move => H s i Hi m.
    move/fallP: H; move/(_ s); move/allP;move/(_ i Hi);move/fallP/(_ m); done.
    move => H; apply/fallP => x; apply/allP => i Hi; apply/fallP => m; apply H.
done.
  Qed.
End Reflections.


Ltac mkPIOA_tac g d st ins outs t :=
  apply (mkPIOA g _ st ins outs d t); [
    by vm_compute | apply/decide_ad_hP; by vm_compute | apply/decide_ad_vP; by vm_compute | apply/ decide_i_aP; by vm_compute ].


(* hiding *)

Section Hiding.
  Context {G D : ctx} (P : PIOA G D) (o : seq (cdom G)) (Ho : all (fun x => x \in (outputs P)) o).

  Check mkPIOA.
  Check tr.
  Check existT.

  Definition hide_tr : St P -> action (D :+: (G |c_ o)) + action G -> option {meas (St P)} :=
    fun s a =>
      match a with
        | inl (existT (inl h) m) => tr P s (inl (mkact D h m))
        | inl (existT (inr h) m) => tr P s (inr (mkact G (ssval h) m))
        | inr (existT c m) => tr P s (inr (mkact G c m))
                 end.

  Check mkPIOA.
  Definition hidePIOA : PIOA G (D :+: (G |c_ o)).
    eapply mkPIOA.
    apply (start P).
    instantiate (2 := seqD (inputs P) o).
    instantiate (1 := seqD (outputs P) o).
    apply/seq_disjointP => x Hx.
    rewrite mem_seqD in Hx; elim (andP Hx) => h1 h2.
    rewrite mem_seqD negb_and h2 //= orbF.
    move/seq_disjointP: (disj_io _ _ P); move/(_ _ h1); done.
    instantiate (2 := hide_tr) => s h m1 m2.
    rewrite //=.
    destruct h.
    apply (ad_h P).
    apply (ad_v P).
    apply (allP Ho).
    apply ssvalP.
    intros.
    eapply (ad_v P).
    rewrite mem_seqD in H0; elim (andP H0); done.
    apply H1.
    done.
    intros; apply i_a.
    rewrite mem_seqD in H0; elim (andP H0); done.
 Defined.
End Hiding.

(* change context *)
Section ChangeH.
  Context {G D D' : ctx} (P : PIOA G D) (H : D' ~~ D).

  Definition changeHTr (s : St P) (a : action D' + action G) :=
    match a with
      | inl h => tr P s (inl (H *a h))
      | inr a => tr P s (inr a)
                     end.

  Definition changeH : PIOA G D'.
    Check mkPIOA.
    apply (mkPIOA
             G
             (St P)
             (start P)
             (inputs P)
             (outputs P)
             D'
             changeHTr).
    apply disj_io.
    simpl.
    move => s h m1 m2.
    rewrite !bijactionE.
    move => h1 h2.
    apply/eqP;
    eapply bijmsg_inj.
    apply/eqP.
    apply (ad_h P s).
    apply h1.
    done.
    simpl.
    apply ad_v.
    apply i_a.
  Defined.
End ChangeH.
