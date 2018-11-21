From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting Aux FastEnum Action.

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

Section Reflections.
  Context (Gamma Delta : ctx) `{FastEnum (cdom Gamma)} `{FastEnum (cdom Delta)} (Hg : forall x, FastEnum (Gamma x)) (Hd : forall x, FastEnum (Delta x)).

  Context (S : finType) `{FastEnum S} (t : S -> (action Delta) + (action Gamma) -> option {meas S}) (inputs outputs : seq (cdom Gamma)) . 
  Definition decide_ad_h :=
    fall (S) (fun s => fall (cdom Delta) (fun h => fall (Delta h) (fun m1 => fall (Delta h) (fun m2 => (t s (inl (mkact Delta h m1)) != None) ==> (t s (inl (mkact Delta h m2)) != None) ==> (m1 == m2))))). 

  Definition decide_ad_v :=
    fall (S ) (fun s => all (fun h => fall (Gamma h) (fun m1 => fall (Gamma h) (fun m2 => (t s (inr (mkact Gamma h m1)) != None) ==> (t  s (inr (mkact Gamma h m2)) != None) ==> (m1 == m2)))) (outputs)).

  Definition decide_i_a :=
    fall (S) (fun s => all (fun i => fall (Gamma i) (fun m => t s (inr (mkact Gamma i m)) != None)) (inputs)).

  Lemma decide_ad_hP : forall (s : S) (h : cdom Delta) (m1 m2 : Delta h),
      t s (inl (mkact Delta h m1)) != None ->
      t s (inl (mkact Delta h m2)) != None ->
      decide_ad_h -> m1 == m2.
    move => s h m1 m2 h1 h2.
    move/fallP; move/(_ s)/fallP/(_ h)/fallP/(_ m1)/fallP/(_ m2)/implyP/(_ h1)/implyP/(_ h2); done.
  Qed.

  Lemma decide_ad_vP : forall (s : S) (h : cdom Gamma) (m1 m2 : Gamma h),
      h \in outputs ->
            t s (inr (mkact Gamma h m1)) != None ->
            t s (inr (mkact Gamma h m2)) != None ->
            decide_ad_v ->
            m1 == m2.
    move => s h m1 m2 Hh h1 h2.
    move/fallP/(_ s)/allP/(_ _ Hh)/fallP/(_ m1)/fallP/(_ m2)/implyP/(_ h1)/implyP/(_ h2); done.
  Qed.

  Lemma decide_i_aP : forall s i, i \in inputs -> forall (m : Gamma i), decide_i_a -> t s (inr (mkact Gamma i m)) != None.
    move => s i Hi m.
    move/fallP/(_ s)/allP/(_ i Hi)/fallP/(_ m); done.
  Qed.

  (* TODO : package into reflection lemma for PIOA_spec, given a pioa_data *)

End Reflections.


(* TODO fix
Ltac mkPIOA_tac g d st ins outs t :=
  apply (mkPIOA g _ st ins outs d t); [
    by vm_compute | apply/decide_ad_hP; by vm_compute | apply/decide_ad_vP; by vm_compute | apply/ decide_i_aP; by vm_compute ].
*)


(* hiding *)

Section Hiding.
  Context {G D : ctx} (P : PIOA G D) (o : seq (cdom G)) (Ho : all (fun x => x \in (outputs P)) o).

  Definition hide_tr : St P -> action (D :+: (G |c_ o)) + action G -> option {meas (St P)} :=
    fun s a =>
      match a with
        | inl (existT (inl h) m) => tr P s (inl (mkact D h m))
        | inl (existT (inr h) m) => tr P s (inr (mkact G (ssval h) m))
        | inr (existT c m) => tr P s (inr (mkact G c m))
                 end.

  Definition hide_tr_data : PIOA_data G (D :+: (G |c_ o)).
    econstructor.
    apply (start P).
    apply (inputs P).
    apply (seqD (outputs P) o).
    apply hide_tr.
  Defined.

  Lemma hidePIOA_spec : PIOA_spec hide_tr_data.
    unfold hide_tr_data; 
  constructor; simpl in *.

    apply/seq_disjointP => x Hx.
    rewrite mem_seqD negb_and.
    move/seq_disjointP: (disj_io (PIOAP P)).
    move/(_ _ Hx) => ->; done.

    rewrite //=.
    destruct h.
    apply (ad_h (PIOAP P)).
    intros.
    eapply ad_v.
    apply (PIOAP P).
    destruct s0; simpl in *.
    move/allP: Ho.
    move/(_ _ ssvalP).
    done.
    apply H0.
    apply H1.

    intros;
    apply (ad_v (PIOAP P) s).
    rewrite mem_seqD in H0; elim (andP H0); done.
    done.
    done.

    intros; apply (i_a (PIOAP P)).
    done.
 Qed.

 Definition hidePIOA : PIOA G (D :+: (G |c_ o)).
   apply (mkPIOA G _ hide_tr_data hidePIOA_spec).
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

  Definition changeH_data : PIOA_data G D'.
  econstructor.
  apply (start P).
  apply (inputs P).
  apply (outputs P).
  apply changeHTr.
  Defined.

  Definition changeH_spec : PIOA_spec changeH_data.
  constructor.
  apply (disj_io (PIOAP P)).

  simpl => s h m1 m2.
  rewrite !bijactionE => h1 h2.
  apply/eqP; eapply bijmsg_inj.
  apply/eqP.
  eapply (ad_h (PIOAP P) s).
  apply h1.
  done.

  simpl; apply (ad_v (PIOAP P)).
  apply (i_a (PIOAP P)).
  Qed.

  Definition changeH : PIOA G D'.
    apply (mkPIOA _ _ changeH_data changeH_spec).
  Defined.
End ChangeH.
