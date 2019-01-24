

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Closure Aux FastEnum Action Posrat.

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
    i_a : forall s i, i \in inputs d -> forall (m : Gamma i), tr d s (inr (mkact Gamma i m)) != None;
    _tr_dist : forall s a mu, tr d s a = Some mu -> isdist mu
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

Lemma tr_isdist {G D : ctx} (P : PIOA G D) s a mu :
  tr P s a = Some mu -> isdist mu.
  elim (PIOAP P); intros.
  eapply _tr_dist0.
  apply H0.
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

Lemma pick_vPn {G D : ctx} (P : PIOA G D) h s :
  pick_v P h s = None -> forall a, tag a = h -> ~~ enabled P s (inr a).
  rewrite /pick_v.
  case: pickP.
  done.
  move => H _ a Ha.
  destruct a; simpl in *.
  subst.
  move: (H s0) => ->; done.
Qed.

Lemma pick_hPn {G D : ctx} (P : PIOA G D) h s :
  pick_h P h s = None -> forall a, tag a = h -> ~~ enabled P s (inl a).
rewrite /pick_h; case: pickP.
done.
move => H _ a Ha.
destruct a; simpl in *.
subst.
move: (H s0) => ->; done.
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

Inductive app_v_spec {G D : ctx} (P : PIOA G D) (v : C P) (s : St P) : Prop :=
  | App_v_ex m mu : tr P s (inr (mkact G v m)) = Some mu -> app_v P v s = (s' <- mu; ret (s', Some (mkact G v m))) -> app_v_spec P v s
  | App_v_nex : (forall a, tag a = v -> ~~ enabled P s (inr a)) -> app_v P v s = (ret (s, None)) -> app_v_spec P v s.

Lemma app_vP {G D : ctx} (P : PIOA G D) (v : C P) (s : St P)
  : v \in outputs P -> app_v_spec P v s.
  move => Hvin.
  remember (app_v P v s) as av; symmetry in Heqav.
  have H2 := Heqav.
  move: H2.
  rewrite /app_v.
  remember (pick_v P v s) as pv; symmetry in Heqpv; destruct pv.
  apply pick_vP in Heqpv.
  destruct s0; simpl in *; move/andP: Heqpv => [h1 h2].
  move/eqP: h2 => h2.
  subst.

  move/opt_neq_none: h1; elim => mu Hmu.
  rewrite Hmu => H.

  eapply App_v_ex.
  apply Hmu.
  rewrite -H; done.
  done.

  move => Heq; apply App_v_nex.
  move => a Ha.
  eapply (pick_vPn P v s) in Heqpv.
  apply Heqpv.
  done.
  rewrite Heqav -Heq //=.
Qed.

Inductive app_h_spec {G D : ctx} (P : PIOA G D) (h : H P) (s : St P) : Prop :=
| App_h_ex m mu : tr P s (inl (mkact D h m)) = Some mu -> app_h P h s = mu -> app_h_spec P h s
| App_h_nex : (forall a, tag a = h -> ~~ enabled P s (inl a)) -> app_h P h s = (ret s) -> app_h_spec P h s.                                                                                         

Lemma app_hP {G D : ctx} (P : PIOA G D) (h : H P) (s : St P) : app_h_spec P h s.
remember (app_h P h s) as ah; symmetry in Heqah.
move: Heqah.
rewrite /app_h.
remember (pick_h P h s) as ph; symmetry in Heqph; destruct ph.
have H2 := Heqph.
apply pick_hP in H2; move/andP: H2 => [h1 h2].
rewrite /enabled in h1.
move/opt_neq_none: h1; elim => mu Hmu.
rewrite Hmu => Heq.
destruct s0; simpl in *.
move: Hmu.
subst.
move: s0 Heqph.
rewrite (eqP h2) {h2} => m Htr.
move => Htr2.
eapply (App_h_ex P h s _ _).
apply Htr2.
rewrite /app_h Htr //= Htr2 //=.
move => Hn.
apply App_h_nex.
move => a Ha.
rewrite /enabled negbK.
rewrite /pick_h in Heqph.
eapply (pick_hPn P h s) in Heqph.
rewrite /enabled negbK in Heqph.
apply Heqph.
done.
rewrite /app_h Heqph //=.
Qed.

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

Definition runFrom {G D : ctx} (P : PIOA G D) (g : seq ((H P) + (C P))) mu :=
  foldl (fun acc x => act P x acc) mu g.

Definition run {G D : ctx} (P : PIOA G D) (g : seq ((H P) + (C P))) :=
  runFrom P g (initDist P).


Definition closed {G D : ctx} (P : PIOA G D) := inputs P == nil.

Lemma run_rcons {G D : ctx} (P : PIOA G D) xs x :
  run P (rcons xs x) = act P x (run P xs).
  rewrite /run /runFrom //=.
  rewrite -cats1 foldl_cat //=.
Qed.

  Lemma runFrom_cat {G D : ctx} (P : PIOA G D) s1 s2 mu :
    runFrom P (s1 ++ s2) mu = runFrom P s2 (runFrom P s1 mu).
    rewrite /runFrom foldl_cat //=.
  Qed.

  Lemma run_cat {G D : ctx} (P : PIOA G D) s1 s2 :
    run P (s1 ++ s2) = runFrom P s2 (run P s1).
    rewrite /run runFrom_cat //=.
  Qed.

Lemma act_bind {G D : ctx} {A : choiceType} (P : PIOA G D) a (m : {meas A}) f :
  act P a (x <- m; f x) = (x <- m; act P a (f x)).
  rewrite /act; case a => x; by rewrite mbindA.
Qed.

Lemma runFrom_mkbind {G D : ctx} (P : PIOA G D) s m :
  runFrom P s m = (x <- m; runFrom P s ( ret x)).
  move: m.
  induction s => m.
  simpl.
  rewrite bind_ret //=.
  rewrite //=.
  rewrite IHs.
  elim a; simpl => x.
  rewrite !measE.
  apply mbind_eqP => y Hy.
  rewrite !measE.
  rewrite IHs measE //=.
  rewrite !measE; apply mbind_eqP => y Hy; rewrite !measE IHs !measE //=.
Qed.

Lemma act_mkbind {G D : ctx} (P : PIOA G D) c m :
  act P c m = (x <- m; act P c (ret x)).
  destruct c; rewrite //=.
  munder (rewrite !measE); done.
  done.
  munder (rewrite !measE); done.
  done.
Qed.

Definition mkPIOA (G D : ctx) (d : PIOA_data G D):
  PIOA_spec d  -> PIOA G D :=
  fun h =>
(Build_PIOA G D d h).



(* usefull lemmas etc *)

Lemma support_app_vP {G D : ctx} (P : PIOA G D) (c : cdom G) (s : St P) y :
  c \in outputs P -> y \in support (app_v P c s) -> (exists s' a, y = (s', Some a) /\ tag a = c) \/ (y = (s, None)).
  intro Hc.
  rewrite /app_v.
  remember (pick_v P c s) as o; destruct o; symmetry in Heqo.
  apply pick_vP in Heqo.
  elim (andP Heqo) => h1 h2.
  remember (tr P s (inr s0)) as t; destruct t.
  move/support_bindP; elim => x.
  elim => h3 h4.
  left.
  exists x.
  exists s0.
  rewrite support_ret mem_seq1 in h4.
  rewrite (eqP h4).
  split; rewrite //=.
  rewrite (eqP h2) //=.
  rewrite support_ret mem_seq1; move/eqP => ->.
  right; done.
  done.
  rewrite support_ret mem_seq1; move/eqP => ->.
  right; done.
Qed.

  Definition v_chan_enabled {G D : ctx} (P : PIOA G D) (c : cdom G) s :=
    [exists m, enabled P s (inr (mkact G c m))].

  Definition v_chan_equienabled {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') (c : cdom G) (s1 : St P) (s2 : St P') :=
    (v_chan_enabled P c s1 = v_chan_enabled P' c s2).

  Definition h_chan_enabled {G D : ctx} (P : PIOA G D) (h : cdom D) s :=
    [exists m, enabled P s (inl (mkact D h m))].

  Definition h_chan_equienabled {G D : ctx} (P P' : PIOA G D) (h : cdom D) (s1 : St P) (s2 : St P') :=
    (h_chan_enabled P h s1 = h_chan_enabled P' h s2).


  Lemma app_v_equienabledP {G D D' : ctx} (P : PIOA G D) (P' : PIOA G D') (Q : {meas St P * option (action G)} -> {meas St P' * option (action G)} -> Prop) c s s' :
    c \in outputs P -> c \in outputs P' ->
    v_chan_equienabled P P' c (s : St P) (s' : St P') ->
    (forall m m' mu mu', tr P s (inr (mkact G c m)) = Some mu ->
                         tr P' s' (inr (mkact G c m')) = Some mu' ->
                         Q (s2 <- mu; ret (s2, Some (mkact G c m))) (s2 <- mu'; ret (s2, Some (mkact G c m')))) ->
    ((forall m, ~~ enabled P s (inr (mkact G c m)) -> ~~ enabled P' s' (inr (mkact G c m))) ->
               Q (ret (s, None)) (ret (s', None))) -> Q (app_v P c s) (app_v P' c s').
    move => Hc1 Hc2.


    rewrite /v_chan_equienabled /v_chan_enabled => H.
    have : (exists m, enabled P s (inr (mkact G c m))) <-> (exists m, enabled P' s' (inr (mkact G c m))).
    split; move/existsP => h; apply/existsP; [ rewrite -H | rewrite H ]; done.
    clear H; move => H.

    move => case1 case2.
    elim: (app_vP P c s); last by done.
    move => m mu Htr ->.

    elim: (app_vP P' c s'); last by done.
    move => m' mu' Htr' ->.
    apply case1; done.

    have Hcon : exists m, enabled P' s' (inr (mkact G c m)).
    apply H.
    exists m.
    rewrite /enabled  Htr //=.
    elim Hcon => mcon Hen.
    move/(_ (mkact G c mcon)).
    rewrite Hen //=;move/(_ erefl); rewrite //=.

    move => H1 ->.
    elim: (app_vP P' c s').
    move => m mu Htr.
    have: exists m, enabled P s (inr (mkact G c m)).
    apply H.
    exists m.
    rewrite /enabled Htr //=.
    elim => Hcon Hen.
    move: (H1 (mkact G c Hcon) erefl); rewrite Hen //=.
    move => H2 ->.
    apply case2 => m.
    move: (H1 (mkact G c m) erefl) ->.
    move => _; apply H2.
    done.
    done.
 Qed.

  

  Lemma app_h_equienabledP {G D : ctx} (P P' : PIOA G D) (Q : {meas St P} -> {meas St P'} -> Prop) h s s' :
    h_chan_equienabled P P' h (s : St P) (s' : St P') ->
    (forall m m' mu mu', tr P s (inl (mkact D h m)) = Some mu ->
                         tr P' s' (inl (mkact D h m')) = Some mu' ->
                         Q mu mu') ->
    ((forall m, ~~ enabled P s (inl (mkact D h m)) -> ~~ enabled P' s' (inl (mkact D h m))) ->
               Q (ret (s)) (ret (s'))) -> Q (app_h P h s) (app_h P' h s').
    rewrite /h_chan_equienabled /h_chan_enabled => H.

    have : (exists m, enabled P s (inl (mkact D h m))) <-> (exists m, enabled P' s' (inl (mkact D h m))).
    split; move/existsP => h1; apply/existsP; [ rewrite -H | rewrite H ]; done.
    clear H; move => H.

    move => case1 case2.
    elim: (app_hP P h s).
    move => m mu Htr ->.

    elim: (app_hP P' h s').
    move => m' mu' Htr' ->.
    eapply case1.
    apply Htr.
    apply Htr'.


    move => Hc.
    have: exists m, enabled P' s' (inl (mkact D h m)).
    apply H.
    exists m.
    rewrite /enabled Htr //=.
    elim => x Hx.
    move: (Hc (mkact D h x) erefl).
    rewrite Hx //=.

    move => H1 ->.
    elim: (app_hP P' h s').
    move => m mu Htr.
    have: exists m, enabled P s (inl (mkact D h m)).
    apply H.
    exists m.
    rewrite /enabled Htr //=.
    elim => Hcon Hen.
    move: (H1 (mkact D h Hcon) erefl).
    rewrite Hen //=.

    move => H2 ->.
    apply case2 => m.
    rewrite H2.
    done.
    done.
 Qed.

  Definition runObsConj {G D : ctx} (P : PIOA G D) (s1 : seq (H P)) (c : C P) (s2 : seq (H P)) mu :=
    runFrom P ((map inl s1) ++ (inr c) :: (map inl s2)) mu.


(* mass lemmas *)

  Check app_h.
Section PIOADist.
  Context {G D : ctx} (P : PIOA G D).

  Check app_h.

Lemma app_h_isdist h s : isdist (app_h P h s).
  case: (app_hP P h s); intros.
  rewrite e0.
  eapply tr_isdist.
  apply e.
  rewrite e isdist_ret //=.
Qed.

Lemma app_v_isdist c s : isdist (app_v P c s).
  rewrite /app_v.
  destruct (pick_v P c s).
  remember (tr P s (inr s0)) as m; destruct m.
  apply isdist_bind.
  eapply tr_isdist; symmetry; apply Heqm.
  intros; apply isdist_ret.
  apply isdist_ret.
  apply isdist_ret.
Qed.

Lemma act_h_isdist h mu : isdist mu -> isdist (act P (inl h) mu).
  intro; simpl.
  apply isdist_bind; rewrite //=.
  intros; apply isdist_bind.
  apply app_h_isdist.
  intros; apply isdist_ret.
Qed.

Lemma act_c_isdist c mu : isdist mu -> isdist (act P (inr c) mu).
  intro; simpl.
  apply isdist_bind; rewrite //=.
  intros; apply isdist_bind.
  apply app_v_isdist.
  intros; apply isdist_ret.
Qed.

Lemma act_isdist hc mu : isdist mu -> isdist (act P hc mu).
  destruct hc.
  apply act_h_isdist.
  apply act_c_isdist.
Qed.

Lemma app_i_isdist s a : isdist (app_i P s a).
  rewrite /app_i.
  remember (tr P a (inr s)) as o; destruct o.
  eapply tr_isdist; symmetry; apply Heqo.
  apply isdist_ret.
Qed.

Check run.

Lemma run_isdist s : isdist (run P s).
  elim/last_ind: s.

  rewrite /run //=.
  rewrite /initDist; apply isdist_ret.

  move => s x H.
  rewrite run_rcons.
  apply act_isdist; done.
Qed.

End PIOADist.

Definition valid_pchan {G D : ctx} (P : PIOA G D) (x : H P + C P) :=
  match x with
  | inl _ => true
               | inr x => x \in outputs P end.

Definition valid_chanseq {G D : ctx} (P : PIOA G D) (x : seq (H P + C P)) :=
  all (valid_pchan P) x.

Definition valid_trace {G D : ctx} (P : PIOA G D) (x : trace P) :=
  all (fun a => tag a \in inputs P ++ outputs P) x.

Definition mvalid {G D : ctx} (P : PIOA G D) (mu : {meas St P * trace P}) :=
  [/\ forall x, x \in support mu -> valid_trace P x.2 & isdist mu].

Definition run_mvalid {G D : ctx} (P : PIOA G D) g :
  valid_chanseq P g ->
  mvalid P (run P g).
  induction g using last_ind.
  simpl.
  rewrite /run //=.
  intro; split.
  move => x; rewrite /initDist in_ret; move/eqP => ->.
  done.
  apply isdist_ret.
  simpl.
  rewrite /valid_chanseq all_rcons; move/andP => [h1 h2].
  rewrite run_rcons; split; simpl.
  intro z.
  destruct x; simpl in *.
  move/support_bindP; elim => mu; elim => Hmu.
  move/support_bindP; elim => Z; elim => HZ.
  rewrite in_ret; move/eqP => heq; subst; simpl in *.
  move: (IHg h2); elim; simpl => h3 h4.
  apply h3.
  done.
  move/support_bindP; elim => mu; elim => Hmu.
  move/support_bindP; elim => Z; elim => HZ.
  rewrite in_ret; move/eqP => heq; subst; simpl in *.
  move: (IHg h2); elim; simpl => h3 h4.
  move/support_app_vP: HZ; move/(_ h1); elim.
  elim => s'; elim => a; elim => heq1 heq2; subst.
  simpl.
  rewrite mem_cat h1 orbT andTb.
  apply h3; done.
  move => ->; simpl.
  apply h3; done.

  apply act_isdist.
  move: (IHg h2).
  elim; done.
Qed.

Ltac pioa_dist_tac :=
  match goal with
    | [ |- None = Some _ -> _ ] => done
    | [ |- Some _ = Some _ -> _ ] => inj; pioa_dist_tac
    | [ |- (if _ then _ else _) = _ -> _ ] => apply if_eq_irrel; pioa_dist_tac
    | [ |- is_true (isdist (ret _)) ] => apply dist_ret
    | _ => idtac
             end.
