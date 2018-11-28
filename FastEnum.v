
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.

Require Import Aux.

Class FastEnum (T : finType) :=
  { fastEnum : seq T;
    fastEnum_ax : perm_eq fastEnum (enum T);
    }.

Lemma fastEnum_uniq {T : finType} `{FastEnum T} : uniq (fastEnum : seq T).
  erewrite perm_eq_uniq.
  apply enum_uniq.
  apply fastEnum_ax.
Qed.

Lemma mem_fastEnum {T : finType} `{FastEnum T} x : x \in (fastEnum : seq T).
  erewrite perm_eq_mem.
  instantiate (1 := enum T); rewrite mem_enum.
  done.
  apply fastEnum_ax.
Qed.

Definition fall (T : finType) `{FastEnum T} (p : pred T) := all p fastEnum.

Lemma fallP (T : finType) `{FastEnum T} (p : pred T) :
  reflect (forall x, p x) (fall T p).
  apply/(iffP idP).
  move/allP => Hx x.
  apply Hx; rewrite //=.
  rewrite mem_fastEnum //=.
  move => Hx; apply/allP => h1 h2; apply Hx.
Qed.


Instance febool : FastEnum [finType of bool] := { fastEnum := [:: true; false]}.
  apply uniq_perm_eq; rewrite ?enum_uniq //=; case; rewrite mem_enum //=.
Defined.

Instance feunit : FastEnum [finType of unit] := { fastEnum := [:: tt ] }.
  apply uniq_perm_eq; rewrite ?enum_uniq //=; case; rewrite mem_enum //=.
Defined.

Instance feoption (T : finType) `{FastEnum T} : FastEnum [finType of option T] :=
  {fastEnum := (None :: map some (fastEnum))}.
  apply uniq_perm_eq; rewrite ?enum_uniq //=.
  apply/andP; split.
  apply/contraT; rewrite negbK => Hc.
  move/mapP: Hc; elim; done.
  rewrite map_inj_uniq.
  apply fastEnum_uniq.
  move => x y Hs; injection Hs; done.
  move => x; destruct x; rewrite //=.
  rewrite mem_enum //=.
  rewrite in_cons mem_map.
  rewrite mem_fastEnum orbT //=.
  move => x y Hs; injection Hs; done.
  rewrite in_cons mem_enum //=.
Defined.

Lemma all_pairs_mem {A B : eqType} (xs : seq A) (ys : seq B) p :
  (p \in [seq (x, y) | x <- xs, y <- ys]) = ((p.1 \in xs) && (p.2 \in ys)).
  induction xs; rewrite //=.
  rewrite mem_cat IHxs .

  have: (p \in [seq (a, y) | y <- ys]) = (p.1 == a) && (p.2 \in ys).
  clear.
  induction ys; rewrite //=.
  rewrite in_nil andbF //=.
  rewrite !in_cons IHys //=.
  destruct p; rewrite //=.
  rewrite xpair_eqE //=.
  rewrite -Bool.andb_orb_distrib_r //=.
  move => ->.
  rewrite in_cons //=.
  case (p.1 == a); case (p.2 \in ys); case (p.1 \in xs); rewrite //=.
Qed.

Instance fepair (T1 T2 : finType) `{FastEnum T1} `{FastEnum T2} :
  FastEnum [finType of T1 * T2] :=
  {fastEnum := [seq (x1, x2) | x1 <- fastEnum, x2 <- fastEnum]}.
  apply uniq_perm_eq; rewrite ?mem_uniq //=.
  apply allpairs_uniq.
  apply fastEnum_uniq.
  apply fastEnum_uniq.
  move => x y Hx Hy.
  rewrite /prod_curry; destruct x; destruct y.
  done.

  apply enum_uniq.

  move => x; rewrite all_pairs_mem !mem_fastEnum mem_enum //=.
Defined.

Instance fesum (T1 T2 : finType) `{FastEnum T1} `{FastEnum T2} :
  FastEnum [finType of T1 + T2] :=
  {fastEnum := (map inl fastEnum ++ map inr fastEnum)}.
  apply uniq_perm_eq; rewrite ?mem_uniq //=.
  rewrite cat_uniq; apply/and3P; split.
  rewrite map_inj_uniq.
  apply fastEnum_uniq.
  move => x y Hs; injection Hs; done.
  apply/hasP; elim => x; move/mapP; elim => y Hy Hy2; move/mapP; elim; intros; subst; done.
  rewrite map_inj_uniq; first by apply fastEnum_uniq.
  move => x y Hs; injection Hs; done.
  apply enum_uniq.

  move => x; destruct x.
  rewrite mem_cat mem_enum //=. 
  have -> : inl s \in [finType of (T1 + T2)%type] by done.
  apply/orP; left; apply/mapP; exists s; first by apply mem_fastEnum.
  done.

  rewrite mem_cat mem_enum //=. 
  have -> : inr s \in [finType of (T1 + T2)%type] by done.
  apply/orP; right; apply/mapP; exists s; first by apply mem_fastEnum.
  done.
Defined.

Definition seqsub {T : choiceType} (s : seq T) (x : T) :=
  match Sumbool.sumbool_of_bool (x \in s) with
    | left Heq => Some (SeqSub Heq)
    | _ => None
             end.


Lemma seqsub_pmap_in {T : choiceType} (s : seq T) x (H : x \in s) :
  (SeqSub H) \in (pmap (seqsub s) (undup s)).
  rewrite mem_pmap.
  apply/mapP.
  exists x.
  rewrite mem_undup //=.
  rewrite /seqsub.
  remember (Sumbool.sumbool_of_bool (x \in s)) as p; rewrite -Heqp; destruct p.
  have -> //= : H = e.
  apply bool_irrelevance.
  have e2 := e.
  rewrite H in e2; done.
Qed.

Instance seq_sub_fe (T : choiceType) (s : seq T) :
  FastEnum ([finType of seq_sub s]) :=
  {fastEnum := pmap (seqsub s) (undup s)}.
  apply uniq_perm_eq; rewrite ?mem_uniq //=.
  eapply pmap_uniq.
  instantiate (1 := fun x => ssval x).
  move => x; rewrite /seqsub //=.
  remember (Sumbool.sumbool_of_bool (x \in s)) as s0; destruct s0; rewrite -Heqs0; done.
  apply undup_uniq.
  apply enum_uniq.
  move => x; rewrite mem_enum //=. 
  have -> : x \in [finType of seq_sub s].
  done.
  destruct x; simpl.
  rewrite seqsub_pmap_in.
  done.
Defined.

Instance fastEnum_bij {A B : finType} {f : A -> B} {g : B -> A} (H : cancel f g) (H2 : cancel g f) `{FastEnum A} : FastEnum B := { fastEnum := map f fastEnum }.
apply uniq_perm_eq.
rewrite map_inj_uniq.
apply fastEnum_uniq.
apply (can_inj H).
apply enum_uniq.
move => x; rewrite mem_enum //=.
have -> : x \in B by done.
apply/mapP.
exists (g x).
apply mem_fastEnum.
rewrite H2 //=.
Defined.