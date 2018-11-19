
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Posrat.

Definition PMeas (A : choiceType) := seq (posrat * A).

Definition integ {A : choiceType} (d : PMeas A) (f : A -> posrat) := \big[padd/0%PR]_(p <- d) (p.1 * f (p.2)).


Lemma integ_nil {A : choiceType} (f : A -> posrat) : integ nil f = 0.
  rewrite /integ.
  rewrite big_nil.
  done.
Qed.

Lemma integ_cons {A : choiceType} (d1 : PMeas A) a f : integ (a :: d1) f = (fst a) * f (snd a) + integ d1 f.
  unfold integ.
  rewrite big_cons.
  done.
Qed.

Definition measReduced {A : choiceType} (M : PMeas A) := 0 \notin (map fst M).
Definition measUnique {A : choiceType} (M : PMeas A) := uniq (map snd M).

Definition nubbed {A : choiceType} (M : PMeas A) :=
  measReduced M && measUnique M.

Fixpoint measAdd {A : choiceType} (M : PMeas A) p (v : A) : PMeas A :=
  if p == 0 then M else
  match M with
    | nil => (p, v) :: nil
    | (p', v') :: m' =>
      if v == v' then (p + p', v) :: m' else (p', v') :: (measAdd m' p v)
                                                      end.

Lemma measAdd_cons {A: choiceType} (M : PMeas A) x p v :
  measAdd (x :: M) p v = if p == 0 then (x :: M) else if v == x.2 then (x.1 + p, v) :: M else x :: measAdd M p v.
 rewrite //=.
 destruct (p == 0); rewrite //=.
 destruct x; rewrite //=.
 rewrite paddrC //=.
Qed.

Check foldl.

Fixpoint measUndup {A : choiceType} (M : PMeas A) :=
  match M with
  | nil => nil
  | (p,v) :: m =>
    measAdd (measUndup m) p v
            end.

Lemma measAddE {A : choiceType} (M : PMeas A) p v f :
  integ (measAdd M p v) f = p * f v + integ M f.
  move: p v.
  induction M => p v.
  rewrite /measAdd.
  elim (eqVneq p 0) => [ -> | hneq].
  rewrite eq_refl integ_nil pmul0r paddr0 //=.
  rewrite (negbTE hneq) integ_cons integ_nil paddr0 //=.
  elim (eqVneq p 0) => [ -> | hneq].
  rewrite measAdd_cons integ_cons pmul0r padd0r //=.
  rewrite measAdd_cons integ_cons (negbTE hneq).
  elim (eqVneq v a.2) => [ -> | hneq2].
  rewrite eq_refl //= integ_cons //=.
  rewrite pmulrDl (paddrC (a.1 * f a.2)) paddrA //=.
  rewrite (negbTE hneq2) integ_cons IHM.
  rewrite paddrC (paddrC (a.1 * f a.2)) paddrA //=.
Qed.

Lemma measAdd_reduced {A : choiceType} (M : PMeas A) p v :
  measReduced M -> measReduced (measAdd M p v).
  rewrite /measReduced.
  move: p v; induction M => p v; rewrite //=.
  elim (eqVneq p 0) => [ -> | hneqp].
  rewrite eq_refl in_nil //=.
  rewrite (negbTE hneqp) //= in_cons in_nil eq_sym (negbTE hneqp) //=.
  elim (eqVneq p 0) => [ -> | hneqp].
  rewrite in_cons negb_or; move/andP; elim => h1 h2; apply/andP; split.
  done.
  done.
  rewrite (negbTE hneqp).
  rewrite in_cons negb_or; move/andP; elim => h1 h2. 
  destruct a.
  elim (eqVneq v s) => [ -> | hneqv].
  rewrite eq_refl //=.
  rewrite in_cons negb_or; apply/andP; split.
  rewrite eq_sym -padd0 (negbTE hneqp); rewrite //= in h1; rewrite (negbTE h1).
  done.
  rewrite (negbTE hneqv) //=.
  rewrite in_cons; rewrite //= in h1; rewrite (negbTE h1) IHM.
  done.
  done.
Qed.

Lemma measAdd_in {A : choiceType} (M : PMeas A) p v x :
  p != 0 -> (x \in (map snd (measAdd M p v))) = (x \in map snd M) || (x == v).
  move: p v;
  induction M; rewrite //= => p v hneqp.
  rewrite (negbTE hneqp) in_cons in_nil orbF //=.
  rewrite (negbTE hneqp).
  destruct a.
  rewrite //=.
  elim (eqVneq v s) => [ -> | hneqx].
  rewrite eq_refl //=.
  rewrite in_cons //=.
  destruct (x == s); rewrite //=.
  rewrite orbF //=.
  rewrite !in_cons (negbTE hneqx) //=.
  rewrite in_cons.
  rewrite IHM.
  elim (eqVneq x s) => [ -> | hneqxs].
  rewrite eq_refl //=.
  rewrite (negbTE hneqxs) !orFb.
  done.
  done.
Qed.

Lemma measAdd_unique {A : choiceType} (M : PMeas A) p v :
  measUnique M -> measUnique (measAdd M p v).
  elim (eqVneq p 0) => [ -> | hneqp].
  rewrite /measUnique; move: v; induction M; rewrite //=.
  rewrite /measUnique; move: v; induction M; rewrite //=.
  rewrite (negbTE hneqp) //=.
  rewrite (negbTE hneqp) //=.
  destruct a => v; rewrite //=.
  elim (eqVneq v s) => [ -> | hneqv].
  rewrite eq_refl //=.
  rewrite (negbTE hneqv) //=.
  rewrite measAdd_in.
  rewrite eq_sym (negbTE hneqv) orbF.
  move/andP => [h1 h2].
  apply/andP; split; rewrite //=.
  apply IHM; done.
  done.
Qed.

Lemma measAdd_nubbed {A : choiceType} (M : PMeas A) p v :
  nubbed M -> nubbed (measAdd M p v).
  rewrite /nubbed.
  move/andP => [h1 h2].
  rewrite measAdd_reduced //=.
  rewrite measAdd_unique //=.
Qed.


Lemma measUndupE {A : choiceType} (M : PMeas A) f :
  integ M f = integ (measUndup M) f.
  move: f.
  induction M => f.
  rewrite integ_nil //=.
  rewrite integ_cons //=.
  destruct a; rewrite //=.
  rewrite measAddE.
  rewrite -IHM.
  done.
Qed.

Lemma measUndup_nubbed {A : choiceType} (M : PMeas A) :
  nubbed (measUndup M).
  induction M; rewrite //=.
  destruct a; apply measAdd_nubbed.
  done.
Qed.

Lemma nubbed_cons {A : choiceType} (M : PMeas A) p :
  nubbed (p :: M) -> nubbed M.
  rewrite /nubbed; move/andP => [h1 h2]; apply/andP; split.
  rewrite /measReduced //= in_cons negb_or in h1.
  move/andP: h1; elim; done.
  rewrite /measUnique //= in h2; move/andP: h2; elim; done.
Qed.

Lemma uniq_proj_uniq {A B : eqType} (xs : seq (A * B)) : uniq (map snd xs) -> uniq xs.
  induction xs; rewrite //=.
  move/andP => [h1 h2].
  rewrite IHxs //= andbT.
  apply/contraT; rewrite negbK => Hc.
  move/mapP: h1; elim.
  exists a; rewrite //=.
Qed.

Definition indicator {A : eqType} (x y : A) := if x == y then 1 else 0.

Lemma integ_nubbed_indicator_in {A : choiceType} (M : PMeas A) p :
  nubbed M -> p \in M -> integ M (indicator p.2) = p.1.
  move: p.
  induction M => p hn hin //=.
  rewrite integ_cons.
  move/orP: hin; elim.
  move/eqP => ->.
  have: integ M (indicator a.2) = 0.
  move: hn; clear; rewrite //= /nubbed.
  move/andP => [h1 h2].
  rewrite /measUnique //= in h2.
  move/andP: h2 => [h21 h22].
  move: h21 h22; clear; induction M ;rewrite //=.
  rewrite integ_nil //=.
  rewrite integ_cons //=.
  move => hn /andP; elim => h1 h2.
  rewrite IHM.
  rewrite in_cons negb_or in hn.
  move/andP: hn => [hn1 hn2].
  rewrite /indicator (negbTE hn1) pmulr0 paddr0 //=.
  rewrite in_cons negb_or in hn; move/andP: hn; elim; done.
  done.
  move => ->.
  rewrite /indicator eq_refl pmulr1 paddr0 //=.
  intros.
  rewrite IHM.
  have: a.2 != p.2.
  move/andP: hn; elim => h1 h2.
  rewrite /measUnique //= in h2; move/andP: h2; elim => h21 h22.
  apply/contraT; rewrite negbK; move/eqP => hc.
  rewrite hc in h21.
  move/mapP: h21; elim.
  exists p; done.
  rewrite /indicator => hneq; rewrite eq_sym (negbTE hneq) pmulr0 padd0r //=.
  eapply nubbed_cons; apply hn.
  done.
Qed.

Lemma integ_indicator_notin {A : choiceType} (M : PMeas A) v :
  v \notin (map snd M) -> integ M (indicator v) = 0.
  induction M; rewrite //=.
  rewrite integ_nil //=.
  rewrite in_cons integ_cons //=.
  rewrite negb_or; move /andP => [h1 h2].
  apply/eqP; rewrite -padd0.
  apply/andP; split; rewrite //=.
  rewrite /indicator (negbTE h1) pmulr0 //=.
  rewrite IHM; done.
Qed.

Lemma integ_nubbed_indicator_in_l {A : choiceType} (M : PMeas A) p :
  nubbed M -> p.1 != 0 -> integ M (indicator p.2) = p.1 -> p \in M.
  intros.
  induction M.
  rewrite integ_nil in H1; rewrite H1 eq_refl in H0; done.
  rewrite integ_cons in H1.
  case (eqVneq p.2 a.2) => [heq | hneq].
  rewrite integ_indicator_notin in H1.
  rewrite paddr0 /indicator heq eq_refl pmulr1 //= in H1.
  rewrite in_cons; destruct a; destruct p; rewrite //=.
  simpl in *.
  subst; rewrite eq_refl //=.
  rewrite heq.
  move/andP: H; elim. 
  rewrite /measUnique //=.
  move => ? /andP; elim; done.
  rewrite /indicator (negbTE hneq) pmulr0 padd0r in H1.
  rewrite in_cons IHM.
  rewrite orbT //=.
  eapply nubbed_cons; apply H.
  done.
Qed.

Lemma nubbedP {A : choiceType} (M1 M2 : PMeas A) :
  nubbed M1 -> nubbed M2 -> (M1 =i M2 <-> (forall f, integ M1 f = integ M2 f)).
  move => nm1 nm2; split; intros.
  have: perm_eq M1 M2.
  apply uniq_perm_eq.
  apply uniq_proj_uniq; move/andP: nm1; elim; done.
  apply uniq_proj_uniq; move/andP: nm2; elim; done.
  done.
  intros.
  rewrite /integ.
  rewrite (eq_big_perm _ x).
  done.

  apply perm_eq_mem.
  rewrite /perm_eq all_cat; apply/andP; split.

  apply/allP => x xin; rewrite //=.
  rewrite !count_uniq_mem.
  have He := integ_nubbed_indicator_in M1 x nm1 xin.
  rewrite H in He.
  have: x \in M2.
  apply integ_nubbed_indicator_in_l; rewrite //=.
  apply/contraT; rewrite negbK => hc.
  move/andP: nm1 => [h1 h2].
  rewrite /measReduced in h1.
  move/mapP: h1; elim.
  exists x.
  done.
  rewrite (eqP hc); done.
  move => ->; rewrite xin; done.
  apply uniq_proj_uniq; move/andP: nm2; elim; done.
  apply uniq_proj_uniq; move/andP: nm1; elim; done.

  apply/allP => x xin; rewrite //=.
  rewrite !count_uniq_mem.
  have He := integ_nubbed_indicator_in M2 x nm2 xin.
  rewrite -H in He.
  have: x \in M1.
  apply integ_nubbed_indicator_in_l; rewrite //=.
  apply/contraT; rewrite negbK => hc.
  move/andP: nm2 => [h1 h2].
  rewrite /measReduced in h1.
  move/mapP: h1; elim.
  exists x.
  done.
  rewrite (eqP hc); done.
  move => ->; rewrite xin; done.
  apply uniq_proj_uniq; move/andP: nm2; elim; done.
  apply uniq_proj_uniq; move/andP: nm1; elim; done.
Qed.

Lemma nubbed_sortedP {A : choiceType} (M1 M2 : PMeas A) :
  nubbed M1 -> nubbed M2 -> canonical_keys M1 -> canonical_keys M2 -> (M1 = M2 <-> (forall f, integ M1 f = integ M2 f)).
  intros; split.
  move => ->; done.
  intros.
  apply canonical_eq_keys; rewrite //=.
  apply nubbedP; rewrite //=.
Qed.

Lemma nubbed_sort_keys {A : choiceType} (M : PMeas A) :
  nubbed M -> nubbed (sort_keys M).
  intro.
  have: perm_eq (sort_keys M) M.
  have: M = undup M.
  symmetry;
  apply undup_id.
  apply uniq_proj_uniq; move/andP: H; elim; done.
  intro heq.
  rewrite {2}heq.
  apply SortKeys.perm.
  intro.

  apply/andP; split.
  rewrite /measReduced.
  erewrite perm_eq_mem.
  move/andP: H; elim => h1 h2; apply h1.
  apply perm_map.
  done.

  rewrite /measUnique.
  erewrite perm_uniq.
  move/andP: H; elim => h1 h2; apply h2.
  apply perm_eq_mem.
  apply perm_map.
  done.

  apply perm_eq_size.
  apply perm_map.
  done.
Qed.


Lemma integ_app {A : choiceType} (d1 d2 : PMeas A) f : integ (d1 ++ d2) f = integ d1 f + integ d2 f.
  unfold integ.
  rewrite big_cat //=.
Qed.


Lemma indicator_eq0 {A : eqType} (x y : A) : (indicator x y == 0) = (x != y).
  rewrite /indicator; case (x == y); done.
Qed.

Lemma indicator_neq0 {A : eqType} (x y : A) : (indicator x y != 0) = (x == y).
  rewrite /indicator; case (x == y); rewrite //=. 
Qed.