
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.

Module FastEnum.

Definition axiom (T : finType) (s : seq T) := perm_eq s (enum T).

Record mixin_of (T : finType) : Type := Mixin { fe : seq T; _ : axiom T fe }.
  
  Section ClassDef.

Record class_of (T : Type) : Type :=
  Class {
      base : Finite.class_of T;
      mixin : mixin_of (Finite.Pack base T);
                       }.
Local Coercion base : class_of >-> Finite.class_of.

Structure type := Pack { sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Check Class.

Definition pack :=
  fun bT (b : Finite.class_of T) m & phant_id (Finite.class bT) b => @Pack T (@Class T b m) T.

Definition finType := @Finite.Pack cT xclass xT.
Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Finite.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Notation fastEnumType := type.
Notation FastEnumType T m := (@pack T _ _ m id).
Notation FastEnumMixin := Mixin.
Notation "[ 'fastEnumType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'fastEnumType' 'of' T 'for' cT ]") : form_scope.
Notation "[ 'fastEnumType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'fastEnumType' 'of' T ]") : form_scope.

End Exports.
End FastEnum.
Import FastEnum.Exports.
Export FastEnum.Exports.

Section FastEnumDefs.
  Variable (T : fastEnumType).
  Definition fastEnum  := FastEnum.fe _ (FastEnum.class T).
  Lemma fastEnum_uniq : uniq (fastEnum).
    rewrite /fastEnum //=.
    destruct T.
    destruct c; rewrite //=.
    destruct mixin; simpl in *.
    erewrite perm_eq_uniq.
    apply enum_uniq.
    rewrite /FastEnum.axiom //= in i.
    apply i.
  Qed.
    
  Lemma fastEnumP : perm_eq fastEnum (enum T). 
    rewrite /fastEnum //=.
    destruct T.
    destruct c; rewrite //=.
    destruct mixin.
    simpl in *.
    done.
  Qed.

  Lemma mem_fastEnum s : s \in fastEnum.
    erewrite perm_eq_mem.
    instantiate (1 := enum T); apply mem_enum.
    apply fastEnumP; rewrite //=.
  Qed.
End FastEnumDefs.


(* bool *)

Lemma fast_enum_bool : FastEnum.axiom _ [:: false; true].
  apply uniq_perm_eq; rewrite ?enum_uniq //=.
  move => x; case x; rewrite mem_enum //=.
Qed.
Canonical boolfastEnumMixin := FastEnumMixin _ [:: false; true] fast_enum_bool.
Canonical boolfastEnumType := FastEnumType _ boolfastEnumMixin.

(* option *)

Lemma fast_enum_option (T : fastEnumType) : FastEnum.axiom _ (None :: map Some (fastEnum T)).
  apply uniq_perm_eq; rewrite ?enum_uniq //=.
  apply/andP; split.
  apply/contraT; rewrite negbK => Hc.
  move/mapP: Hc; elim; done.
  rewrite map_inj_uniq.
  apply fastEnum_uniq.
  move => x y H; injection H; done.
  move => x; destruct x; rewrite //=.
  rewrite mem_enum //=.
  rewrite in_cons mem_map.
  rewrite (perm_eq_mem (fastEnumP T)) mem_enum //=.
  move => x y H; injection H; done.
  rewrite in_cons mem_enum //=.
Qed.
Canonical optionfastEnumMixin (T : fastEnumType) := FastEnumMixin _ (None :: map Some (fastEnum T)) (fast_enum_option T).
Canonical optionfastEnumType (T : fastEnumType) := FastEnumType _ (optionfastEnumMixin T).

(* pair *)

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


Lemma fast_enum_pair (T1 T2 : fastEnumType) : FastEnum.axiom _ ([seq (x1, x2) | x1 <- fastEnum T1, x2 <- fastEnum T2]).
  apply uniq_perm_eq; rewrite ?mem_uniq //=.
  apply allpairs_uniq.
  apply fastEnum_uniq.
  apply fastEnum_uniq.
  move => x y Hx Hy.
  rewrite /prod_curry; destruct x; destruct y.
  done.

  apply enum_uniq.

  move => x; rewrite all_pairs_mem; rewrite (perm_eq_mem (fastEnumP T1)) (perm_eq_mem (fastEnumP T2)) !mem_enum //=.
Qed.

Canonical pairfastEnumMixin (T1 T2 : fastEnumType) := FastEnumMixin _ [seq (x, y) | x <- fastEnum T1, y <- fastEnum T2] (fast_enum_pair T1 T2).
Canonical pairfastEnumType (T1 T2 : fastEnumType) := FastEnumType _ (pairfastEnumMixin T1 T2).

