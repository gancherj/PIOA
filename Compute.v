(* Reflection lemmas and computation lemmas for PIOAs *)


From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Lifting Aux FastEnum Action PIOA CompPIOA.

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

(* app_h / app_ova *)

Print app_h.
Print pick_h.

Lemma ohead_some A (xs : seq A) a : ohead xs = Some a -> exists t, xs = a :: t.
case xs; rewrite //=.
move => a0 l H.
injection H => heq; subst.
exists l; done.
Qed.

Lemma ohead_none A (xs : seq A) : ohead xs = None -> xs = nil.
case xs; rewrite //=.
Qed.

Definition pick_fast (T : finType) `{FastEnum T} (P : pred T) :=
  ohead (filter P fastEnum).

Lemma pick_fastP (T : finType) `{FastEnum T} (P : pred T) : pick_spec P (pick_fast T P).
  remember (pick_fast T P) as o; destruct o; symmetry in Heqo.
  apply Pick.
  rewrite /pick_fast in Heqo.
  apply ohead_some in Heqo; elim Heqo => x Hx.
  have : s \in filter P (fastEnum).
  rewrite Hx in_cons eq_refl //=.
  rewrite mem_filter; move/andP; elim; done.

  apply ohead_none in Heqo; rewrite /pick_fast in Heqo.
  apply Nopick.
  move => x.
  remember (P x) as b; destruct b.
  have: x \in filter P fastEnum.
  rewrite mem_filter -Heqb mem_fastEnum //=.
  rewrite Heqo in_nil //=.
  done.
Qed.

Print pick_h.

Definition pick_h_fast (G D : ctx) (P : PIOA G D) (h : H P) (x : St P) `{FastEnum (D h)} :=
  (pick_fast (D h) (fun m => enabled P x (inl (mkact D h m)))) <$>o (fun m => mkact D h m).

Print pick_v.

Definition pick_v_fast (G D : ctx) (P : PIOA G D) (h : C P) (x : St P) `{FastEnum (G h)} :=
  (pick_fast (G h) (fun m => enabled P x (inr (mkact G h m)))) <$>o (fun m => mkact G h m).

Lemma pick_h_fastE (G D : ctx) (P : PIOA G D) (h : H P) (x : St P) `{FastEnum (D h)} :
   pick_h P h x = pick_h_fast G D P h x.
rewrite /pick_h /pick_h_fast.
have -> //=: [pick m | enabled P x (inl (mkact D h m)) ] =
      pick_fast (D h) (fun m : D h => enabled P x (inl (mkact D h m))).
case:pickP; case:pick_fastP.
move=> m1 Hm1 m2 Hm2.
Check actDeterm_h.
Check (ad_h (PIOAP P)).
have: m1 == m2.
apply (ad_h (PIOAP P) x).
done.
done.
move/eqP => -> //=.

move => Hn m1 Hm1.
have Hc := Hn m1; rewrite Hm1 in Hc; done.

move => m1 Hm1 Hn.
have Hc := Hn m1; rewrite Hm1 in Hc; done.
done.
Qed.

Lemma pick_v_fastE (G D : ctx) (P : PIOA G D) (h : C P) (x : St P) `{FastEnum (G h)} :
  h \in outputs P ->
   pick_v P h x = pick_v_fast G D P h x.
  intro Hh.
rewrite /pick_v /pick_v_fast.
have -> //=: [pick m | enabled P x (inr (mkact G h m)) ] =
      pick_fast (G h) (fun m : G h => enabled P x (inr (mkact G h m))).
case:pickP; case:pick_fastP.
move=> m1 Hm1 m2 Hm2.
have: m1 == m2.
apply (ad_v (PIOAP P) x).
done.
done.
done.
move/eqP => -> //=.

move => Hn m1 Hm1.
have Hc := Hn m1; rewrite Hm1 in Hc; done.

move => m1 Hm1 Hn.
have Hc := Hn m1; rewrite Hm1 in Hc; done.
done.
Qed.

  
Definition app_h_fast {G D : ctx} (P : PIOA G D) (h : H P) (x : St P) `{FastEnum (D h)} :=
  oapp (fun ha => oapp id (ret x) (tr P x (inl ha))) (ret x) (pick_h_fast _ _ P h x).

Lemma app_h_fastE {G D : ctx} (P : PIOA G D) (h : H P) (x : St P) `{FastEnum (D h)} :
  app_h P h x = app_h_fast P h x.
  rewrite /app_h /app_h_fast pick_h_fastE //=.
Qed.

Check oapp.

(* NOTE: use simpl, note rewrite //= !! *)
Definition app_v_fast {G D : ctx} (P : PIOA G D) (v : C P) (s : St P) `{FastEnum (G v)} :=
  oapp (fun va =>
          oapp (fun mu => (x <- mu; ret (x, Some va))) (ret (s, None)) (tr P s (inr va))) (ret (s, None)) (pick_v_fast _ _ P v s).

Lemma app_v_fastE {G D : ctx} (P : PIOA G D) (v : C P) (s : St P) `{FastEnum (G v)} :
  v \in outputs P ->
  app_v P v s = app_v_fast P v s.
  move => Hv.
  rewrite /app_v /app_v_fast.
  rewrite pick_v_fastE.
  simpl.
  destruct (pick_v_fast G D P v s); simpl.
  destruct (tr P s (inr s0)); simpl; done.
  done.
  done.
Qed.

(* TODO: provide computation rules for:

(this is already
*)

(*
Check pick_h.

Lemma pick_h_compP {G D D' : ctx} (P1 : PIOA G D) (P2 : PIOA G D') (h : H P1) (x : St P1) y :
  pick_h (P1 ||| P2) (inl h) (x,y) = ((pick_h P1 h x) <$>o (fun m => Some (mkact (D :+: D') (inl h) m))).
*)