
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
Open Scope R.
Import GRing.Theory.
Import Num.Theory.

Definition Qnneg := [qualify a x : rat | 0 <= x].
Lemma Qnneg_def x : (x \is a Qnneg) = (0 <= x).
  done.
Qed.

Fact Qnneg_key : pred_key Qnneg. done. Qed.
Canonical Qnneg_keyed := KeyedQualifier Qnneg_key.

Section PosRatDef.
  Record posrat :=
    Posrat {
        mprat :> rat;
        _ : mprat \is a Qnneg}.

  Canonical Structure posratSub := [subType for mprat].
    Definition pEqmix := [eqMixin of posrat by <:].
    Canonical Structure pEqtype := EqType posrat pEqmix.
    Definition pChoicemix := [choiceMixin of posrat by <: ].
    Canonical pChoisetype := ChoiceType posrat pChoicemix.

End PosRatDef.

Definition padd (a b : posrat) : posrat.
  destruct a,b.
  econstructor.
  instantiate (1 := mprat0 + mprat1).
  apply Num.Theory.addr_ge0; done.
Defined.

Definition pmul (a b : posrat) : posrat.
  destruct a,b.
  econstructor.
  instantiate (1 := mprat0 * mprat1).
  apply Num.Theory.mulr_ge0; done.
Defined.

Lemma pmulrA : @associative posrat pmul.
move=> x y z; apply/eqP; rewrite /pmul /eq_op //=; destruct x,y,z; rewrite //=; rewrite mulrA.
done.
Qed.

Lemma paddrA : @associative posrat padd.
move=> x y z; apply/eqP; rewrite /padd /eq_op //=; destruct x,y,z; rewrite //=; rewrite addrA.
done.
Qed.



Lemma pmul1r : @left_id posrat posrat (Posrat 1 is_true_true) pmul.
move=>x; destruct x; apply/eqP; rewrite /pmul /eq_op //=; rewrite mul1r; done.
Qed.

Lemma pmulr1 : @right_id posrat posrat (Posrat 1 is_true_true) pmul.
move=>x; destruct x; apply/eqP; rewrite /pmul /eq_op //=; rewrite mulr1; done.
Qed.

Lemma pmul0r : @left_zero posrat posrat (Posrat 0 is_true_true) pmul.
move=>x; destruct x; apply/eqP; rewrite /pmul /eq_op //=; rewrite mul0r; done.
Qed.

Lemma pmulr0 : @right_zero posrat posrat (Posrat 0 is_true_true) pmul.
move=>x; destruct x; apply/eqP; rewrite /pmul /eq_op //=; rewrite mulr0; done.
Qed.

Lemma padd0r : @left_id posrat posrat (Posrat 0 is_true_true) padd.
move=>x; destruct x; apply/eqP; rewrite /padd /eq_op //=; rewrite add0r; done.
Qed.

Lemma paddr0 : @right_id posrat posrat (Posrat 0 is_true_true) padd.
move=>x; destruct x; apply/eqP; rewrite /padd /eq_op //=; rewrite addr0; done.
Qed.

Lemma pmulrDl : @left_distributive posrat posrat pmul padd.
move=> x y z; destruct x,y,z; apply/eqP; rewrite /pmul /padd /eq_op //=; rewrite mulrDl; done.
Qed.

Lemma pmulrDr : @right_distributive posrat posrat pmul padd.
move=> x y z; destruct x,y,z; apply/eqP; rewrite /pmul /padd /eq_op //=; rewrite mulrDr; done.
Qed.

Lemma pmulrC : @commutative posrat posrat pmul.
move=> x y; destruct x,y; apply/eqP; rewrite /pmul /eq_op //=; rewrite mulrC; done.
Qed.

Lemma paddrC : @commutative posrat posrat padd.
move=> x y; destruct x,y; apply/eqP; rewrite /padd /eq_op //=; rewrite addrC; done.
Qed.



Canonical padd_monoid := Monoid.Law paddrA padd0r paddr0.
Canonical padd_comid := Monoid.ComLaw paddrC.
Canonical pmul_monoid := Monoid.Law pmulrA pmul1r pmulr1.
Canonical pmul_muloid := Monoid.MulLaw pmul0r pmulr0.
Canonical pmul_addoid := Monoid.AddLaw pmulrDl pmulrDr.
Canonical pmul_comid := Monoid.ComLaw pmulrC.

Notation "x + y" := (padd x y) : posrat_scope.
Notation "x * y" := (pmul x y) : posrat_scope.
Notation "0" := (Posrat 0 is_true_true) : posrat_scope.
Notation "1" := (Posrat 1 is_true_true) : posrat_scope.

Delimit Scope posrat_scope with PR.

Open Scope PR.
Import Monoid.Theory.
  

Lemma pmul0 (x y : posrat) : (x == 0) || (y == 0) = (x * y == 0).
  destruct x,y.
  apply /eqP; rewrite /eq_op //=.
  destruct (eqVneq mprat0 0).
  subst.
  simpl.
  rewrite mul0r; done.

  destruct (eqVneq mprat1 0).
  subst.
  simpl; rewrite eq_refl orbT mulr0 eq_refl; done.
  Check GRing.mulf_eq0.
  have H := (GRing.mulf_eq0 mprat0 mprat1).
  rewrite (negbTE i1) in H.
  rewrite (negbTE i2) in H.
  simpl in H.
  rewrite H.
  rewrite (negbTE i1).
  rewrite (negbTE i2).
  simpl.
  done.
Qed.

Lemma padd0 (x y : posrat) : (x == 0) && (y == 0) = (x + y == 0).
  destruct x,y.
  apply /eqP; rewrite /eq_op //=.
  destruct (eqVneq mprat0 0).
  subst.
  destruct (eqVneq mprat1 0).

  subst.
  simpl.
  rewrite add0r.
  done.
  rewrite eq_refl (negbTE i1) add0r.
  done.

  destruct (eqVneq mprat1 0).
  subst.
  rewrite (negbTE i1).
  simpl.
  rewrite addr0.
  done.

  rewrite (negbTE i1) (negbTE i2).
  simpl.
  rewrite Qnneg_def in i.
  rewrite Qnneg_def in i0.
  have: (0 < mprat0 + mprat1)%R .

  apply addr_gt0.
  rewrite ltr_def i i1; done.
  rewrite ltr_def i0 i2; done.
  intros.
  rewrite ltr_def in x.
  move/andP: x => [x0 x1].
  rewrite (negbTE x0).
  done.
Qed.

Definition pdiv (a b : posrat) : posrat.
  destruct a,b.
  econstructor.
  instantiate (1 := mprat0 / mprat1).
  rewrite Qnneg_def.
  apply divr_ge0.
  done.
  done.
Defined.

Notation "x / y" := (pdiv x y) : posrat_scope.

Definition posrat_of_nat (x : nat) : posrat.
  econstructor.
  instantiate (1 := x%:Q).
  rewrite Qnneg_def.
  apply ler0n.
Defined.

Definition ple (a b : posrat) : bool.
  destruct a,b.
  exact (mprat0 <= mprat1).
Defined.

Notation "x <= y" := (ple x y) : posrat_scope.

Lemma ple_le0 a : (a <= 0) = (a == 0).
  have: (a <= 0) <-> (a == 0).
  split.
  destruct a; simpl; intros; apply/eqP.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  apply/eqP; rewrite eqr_le.
  apply/andP; split; done.

  intro H; rewrite (eqP H); done.

  intros.
  apply/iffP.
  apply idP.
  apply x.
  apply x.
  destruct (a == 0); done.
Qed.

Lemma ple_refl a : a <= a.
  destruct a; simpl; done.
Qed.

Lemma ple_antisymm a b : a <= b -> b <= a -> a = b.
  destruct a,b; simpl.
  intros.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  apply/eqP;
  rewrite eqr_le.
  apply/andP; split; done.
Qed.

Lemma ple_trans a b c : a <= b -> b <= c -> a <= c.
  destruct a,b,c; simpl.
  apply ler_trans.
Qed.

Lemma ple_total a b : (a <= b) || (b <= a).
  destruct a,b;simpl.
  apply ger_leVge.
  rewrite Qnneg_def in i; done.
  rewrite Qnneg_def in i0; done.
Qed.

Lemma ple_add_r a b c : a <= b -> a + c <= b + c.
  destruct a,b,c; simpl.
  intros.
  apply ler_add.
  done.
  done.
Qed.

Lemma ple_add_l a b c : a <= b -> c + a <= c + b.
 rewrite (paddrC c a).
 rewrite (paddrC c b).
 apply ple_add_r.
Qed.

Lemma ple_add_lr a b c d : a <= b -> c <= d -> a + c <= b + d.
 intros.
 eapply ple_trans.
 instantiate (1 := b + c).
 apply ple_add_r; done.
 apply ple_add_l; done.
Qed.

Lemma ple_mul_r a b c : a <= b -> a * c <= b * c.
  destruct a,b,c; simpl.
  intros.
  eapply ler_pmul.
  done.
  done.
  done.
  done.
Qed.

Lemma ple_mul_l a b c : a <= b -> c * a <= c * b.
 rewrite (pmulrC c a).
 rewrite (pmulrC c b).
 apply ple_mul_r.
Qed.

Lemma ple_mul_lr a b c d : a <= b -> c <= d -> a * c <= b * d.
  destruct a,b,c,d ;simpl; intros.
  apply ler_pmul; done.
Qed.

Definition pdist (a b : posrat) : posrat.
  destruct a,b.
  econstructor.
  instantiate (1 := `|mprat0 - mprat1|).
  rewrite Qnneg_def.
  apply normr_ge0.
Defined.

Lemma pdist_eq0 a b : (pdist a b == 0) = (a == b).
  apply/(iffP idP).
  instantiate (1 := (a == b)).
  rewrite /pdist.
  destruct a,b.
  intro.
  rewrite /eq_op //=; apply/eqP.
  rewrite /eq_op //= in H.
  rewrite normr_eq0 in H.
  rewrite subr_eq0 in H.
  apply/eqP; done.
  intro H; rewrite (eqP H).
  rewrite /pdist.
  destruct b; simpl.
  rewrite /eq_op //=; apply/eqP.
  apply/eqP; rewrite normr_eq0.
  rewrite subr_eq0.
  done.
  destruct (a == b); done.
Qed.

Lemma pdist_le0 a b : (pdist a b <= 0) = (a == b).
  apply/(iffP idP).
  instantiate (1 := a == b).
  intro.
  rewrite ple_le0 in H.
  rewrite pdist_eq0 in H.
  done.
  intro.
  rewrite ple_le0.
  rewrite pdist_eq0.
  done.
  destruct (a == b); done.
Qed.

Lemma pdist_symm a b : pdist a b = pdist b a.
  rewrite /pdist; destruct a,b.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  rewrite distrC; done.
Qed.

Lemma pdist_triangle a b c : pdist a c <= pdist a b + pdist b c.
  rewrite /pdist; destruct a,b, c.
  simpl.
  apply ler_dist_add.
Qed.

Lemma pdist_add_r a b c : pdist a b = pdist (a + c) (b + c).
  rewrite/pdist; destruct a,b,c; simpl.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  rewrite (addrC mprat1 mprat2).
  rewrite GRing.addrKA.
  done.
Qed.

Lemma pdist_add_l a b c : pdist a b = pdist (c + a) (c + b).
  rewrite (paddrC c a).
  rewrite (paddrC c b).
  apply pdist_add_r.
Qed.

Lemma pdist_add_lr a b c d : pdist (a + c) (b + d) <= pdist a b + pdist c d.

  rewrite/pdist; destruct a,b,c,d; simpl.
  have: mprat0 + mprat2 - (mprat1 + mprat3) =
        ((mprat0 - mprat1) + (mprat2 - mprat3))%R.
  rewrite -mulN1r.
  rewrite mulrDr.
  rewrite !mulN1r.
  rewrite addrA.
  rewrite addrA.
  congr (_ + _)%R.
  rewrite -addrA.
  rewrite (addrC mprat2 (-mprat1)).
  rewrite addrA.
  done.
  intro.
  rewrite x.
  apply ler_norm_add.
Qed.

Lemma pdist_mul_l a b c : pdist (c * a) (c * b) = c * (pdist a b).
  rewrite/pdist;destruct a,b,c; simpl.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  have: mprat2 * mprat0 - mprat2 * mprat1 =
        (mprat2 * (mprat0 - mprat1))%R.
  rewrite -mulN1r.
  rewrite mulrA.
  rewrite (mulrC (-1) mprat2).
  rewrite -mulrA.
  rewrite -mulrDr.
  rewrite mulN1r.
  done.
  intro.
  rewrite x.
  rewrite normrM.
  have: `|mprat2| == mprat2.
  rewrite -ger0_def.
  done.
  intro H; rewrite (eqP H).
  done.
Qed.

Lemma pdist_mul_r a b c : pdist (a * c) (b * c) = c * (pdist a b).
  rewrite (pmulrC a c).
  rewrite (pmulrC b c).
  apply pdist_mul_l.
Qed.

Lemma ple_sum {A} (c : seq A) (F1 F2 : A -> posrat) :
  (forall x, F1 x <= F2 x) ->
  (\big[padd/0]_(p <- c) F1 p) <= (\big[padd/0]_(p <- c) F2 p).
  intros.
  induction c.
  rewrite !big_nil; done.
  rewrite !big_cons.
  apply ple_add_lr.
  done.
  done.
Qed.  