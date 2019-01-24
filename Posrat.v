
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

Definition padd_ (a b : posrat) : posrat.
  destruct a,b.
  econstructor.
  instantiate (1 := mprat0 + mprat1).
  apply Num.Theory.addr_ge0; done.
Defined.

Definition padd a b := locked (padd_ a b).

Definition pmul_ (a b : posrat) : posrat.
  destruct a,b.
  econstructor.
  instantiate (1 := mprat0 * mprat1).
  apply Num.Theory.mulr_ge0; done.
Defined.

Definition pmul a b := locked (pmul_ a b).

Lemma pmulrA : @associative posrat pmul.
  unlock pmul.
move=> x y z; apply/eqP; rewrite /pmul /eq_op //=; destruct x,y,z; rewrite //=; rewrite mulrA.
done.
Qed.

Lemma paddrA : @associative posrat padd.
  unlock padd.
move=> x y z; apply/eqP; rewrite /padd /eq_op //=; destruct x,y,z; rewrite //=; rewrite addrA.
done.
Qed.


Lemma pmul1r : @left_id posrat posrat (Posrat 1 is_true_true) pmul.
  unlock pmul;
move=>x; destruct x; apply/eqP; rewrite /pmul /eq_op //=; rewrite mul1r; done.
Qed.

Lemma pmulr1 : @right_id posrat posrat (Posrat 1 is_true_true) pmul.
  unlock pmul;
move=>x; destruct x; apply/eqP; rewrite /pmul /eq_op //=; rewrite mulr1; done.
Qed.

Lemma pmul0r : @left_zero posrat posrat (Posrat 0 is_true_true) pmul.
  unlock pmul;
move=>x; destruct x; apply/eqP; rewrite /pmul /eq_op //=; rewrite mul0r; done.
Qed.

Lemma pmulr0 : @right_zero posrat posrat (Posrat 0 is_true_true) pmul.
  unlock pmul;
move=>x; destruct x; apply/eqP; rewrite /pmul /eq_op //=; rewrite mulr0; done.
Qed.

Lemma padd0r : @left_id posrat posrat (Posrat 0 is_true_true) padd.
  unlock padd pmul;
move=>x; destruct x; apply/eqP; rewrite /padd /eq_op //=; rewrite add0r; done.
Qed.

Lemma paddr0 : @right_id posrat posrat (Posrat 0 is_true_true) padd.
  unlock padd pmul;
move=>x; destruct x; apply/eqP; rewrite /padd /eq_op //=; rewrite addr0; done.
Qed.

Lemma pmulrDl : @left_distributive posrat posrat pmul padd.
  unlock padd pmul;
move=> x y z; destruct x,y,z; apply/eqP; rewrite /pmul /padd /eq_op //=; rewrite mulrDl; done.
Qed.

Lemma pmulrDr : @right_distributive posrat posrat pmul padd.
  unlock padd pmul;
move=> x y z; destruct x,y,z; apply/eqP; rewrite /pmul /padd /eq_op //=; rewrite mulrDr; done.
Qed.

Lemma pmulrC : @commutative posrat posrat pmul.
  unlock padd pmul;
move=> x y; destruct x,y; apply/eqP; rewrite /pmul /eq_op //=; rewrite mulrC; done.
Qed.

Lemma paddrC : @commutative posrat posrat padd.
  unlock padd pmul;
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
  apply/eqP.
  unlock pmul.
  simpl.
  rewrite mul0r; done.

  destruct (eqVneq mprat1 0).
  subst.
  unlock pmul.
  simpl; rewrite eq_refl orbT mulr0 eq_refl; done.
  Check GRing.mulf_eq0.
  have H := (GRing.mulf_eq0 mprat0 mprat1).
  rewrite (negbTE i1) in H.
  rewrite (negbTE i2) in H.
  simpl in H.
  unlock pmul.
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
  unlock padd; simpl.
  rewrite add0r.
  done.
  unlock padd; simpl. rewrite (negbTE i1) add0r.
  done.

  destruct (eqVneq mprat1 0).
  subst.
  rewrite (negbTE i1).
  simpl.
  unlock padd; simpl; rewrite addr0.
  done.

  rewrite (negbTE i1) (negbTE i2).
  simpl.
  unlock padd; simpl; rewrite Qnneg_def in i.
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

Definition pinv_ (a : posrat) : posrat.
  destruct a.
  econstructor.
  instantiate (1 := mprat0^-1).
  rewrite Qnneg_def.
  rewrite invr_ge0.
  rewrite -Qnneg_def; done.
Defined.

Definition pinv a := locked (pinv_ a).


Definition pexp_ (a : posrat) (n : nat) : posrat.
  destruct a.
  econstructor.
  instantiate (1 := mprat0 ^+ n).
  rewrite Qnneg_def.
  apply exprn_ge0.
  done.
Defined.

Definition pexp a n := locked (pexp_ a n).

Notation "x / y" := (x * (pinv y)) : posrat_scope.

Notation "x ^+ n" := (pexp x n) : posrat_scope.

Lemma pexp_S (a : posrat) (n : nat) :
  a ^+ (S n) =
  a * (a ^+ n).
  unlock pexp.
  destruct a; simpl.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  unlock pmul.
  unlock pexp.
  rewrite exprS.
  simpl.
  done.
Qed.

Lemma pexp1 (x  :posrat) : x ^+ 1 = x.
destruct x.
unlock pexp.
apply/eqP; rewrite /eq_op //=.
Qed.

Definition posrat_of_nat_ (x : nat) : posrat.
  econstructor.
  instantiate (1 := x%:Q).
  rewrite Qnneg_def.
  apply ler0n.
Defined.

Definition posrat_of_nat x := locked (posrat_of_nat_ x).

Definition ple (a b : posrat) : bool.
  destruct a,b.
  exact (mprat0 <= mprat1).
Defined.

Definition plt (a b : posrat) : bool.
  destruct a,b.
  exact (mprat0 < mprat1).
Defined.

Notation "x <= y" := (ple x y) : posrat_scope.
Notation "x < y" := (plt x y) : posrat_scope.

Definition plt_def (a b : posrat) : (a < b) = ((a != b) && (a <= b)).
  destruct a,b.
  rewrite /plt.
  rewrite /ple.
  rewrite /eq_op //=.
  rewrite ltr_def //=.
  rewrite eq_sym.
  done.
Qed.

Lemma plt_trans (a b c : posrat) : a < b -> b < c -> a < c.
  destruct a,b,c; rewrite /plt.
  apply ltr_trans.
Qed.

Lemma plt_add (a b c d : posrat) : a < b -> c < d -> a + c < b + d.
  destruct a,b,c,d; rewrite /plt.
  unlock padd.
  apply ltr_add.
Qed.

Lemma plt_mulr (a  c d : posrat) : a != 0 -> c < d -> a * c < a * d.
  destruct a,c,d; rewrite /plt.
  simpl.
  intros.

  unlock pmul; simpl.
  rewrite (mulrC mprat0).
  rewrite (mulrC mprat0).
  rewrite ltr_pmul2r.
  done.
  rewrite ltr_def.
  rewrite H.
  rewrite -Qnneg_def; done.
Qed.

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

Lemma ple_add_is_le a b c : a + b <= c -> (a <= c) && (b <= c).
  destruct a,b,c.
  unfold ple.
  simpl.
  unlock padd; simpl.
  intro; apply/andP; split.
  apply/contraT.
  rewrite -real_ltrNge.
  unlock padd in H; simpl in H.
  rewrite real_lerNgt in H.
  intro.

  have: (mprat2 < mprat0 + mprat1)%R.
  remember (mprat1 == 0) as b; symmetry in Heqb; destruct b.
  rewrite (eqP Heqb) addr0; done.
  rewrite -(addr0 mprat2).
  apply ltr_add.
  done.
  rewrite ltr_def.
  rewrite Heqb.
  rewrite Qnneg_def in i0.
  rewrite i0.
  done.
  rewrite (negbTE H); done.
  rewrite realE; apply/orP; left.
  apply addr_ge0.
  rewrite Qnneg_def in i; done.
  rewrite Qnneg_def in i0; done.
  rewrite realE; apply/orP; left; rewrite Qnneg_def in i1; done.
  rewrite realE; apply/orP; left; rewrite Qnneg_def in i1; done.
  rewrite realE; apply/orP; left; rewrite Qnneg_def in i; done.

  apply/contraT.
  rewrite -real_ltrNge.
  rewrite real_lerNgt in H.
  intro.

  have: (mprat2 < mprat0 + mprat1)%R.
  remember (mprat0 == 0) as b; symmetry in Heqb; destruct b.
  rewrite (eqP Heqb) add0r; done.
  rewrite -(addr0 mprat2) -(addrC 0%R mprat2).
  apply ltr_add.
  rewrite ltr_def Heqb.
  rewrite Qnneg_def in i; rewrite i; done.
  done.
  rewrite (negbTE H); done.

  rewrite realE; apply/orP; left.
  apply addr_ge0.
  rewrite Qnneg_def in i; done.
  rewrite Qnneg_def in i0; done.
  rewrite realE; apply/orP; left; rewrite Qnneg_def in i1; done.
  rewrite realE; apply/orP; left; rewrite Qnneg_def in i1; done.
  rewrite realE; apply/orP; left; rewrite Qnneg_def in i; done.
Qed.

Lemma ple_add_r a b c : a <= b -> a + c <= b + c.
  destruct a,b,c; simpl.
  unlock padd.
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
  unlock pmul; simpl.
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
  unlock pmul; simpl.
  apply ler_pmul; done.
Qed.

Definition pdist_ (a b : posrat) : posrat.
  destruct a,b.
  econstructor.
  instantiate (1 := `|mprat0 - mprat1|).
  rewrite Qnneg_def.
  apply normr_ge0.
Defined.

Definition pdist a b := locked (pdist_ a b).

Lemma pdist_eq0 a b : (pdist a b == 0) = (a == b).
  unlock pdist.
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
  unlock pdist.
  rewrite /pdist_; destruct a,b.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  rewrite distrC; done.
Qed.

Lemma pdist_triangle a b c : pdist a c <= pdist a b + pdist b c.
  unlock pdist;
  rewrite /pdist_; destruct a,b, c.
  simpl.
  unlock padd.
  simpl.
  apply ler_dist_add.
Qed.

Lemma pdist_add_r a b c : pdist a b = pdist (a + c) (b + c).
  unlock pdist;
  rewrite/pdist_; destruct a,b,c; simpl.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  unlock padd; simpl.
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

  unlock pdist;
  rewrite/pdist_; destruct a,b,c,d; simpl.
  have: (mprat0 + mprat2 - (mprat1 + mprat3))%R =
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
  unlock padd; simpl.
  rewrite x.
  apply ler_norm_add.
Qed.

Lemma pdist_mul_l a b c : pdist (c * a) (c * b) = c * (pdist a b).
  unlock pdist; 
  rewrite/pdist_;destruct a,b,c; simpl.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
  have: (mprat2 * mprat0 - mprat2 * mprat1)%R =
        (mprat2 * (mprat0 - mprat1))%R.
  rewrite -mulN1r.
  rewrite mulrA.
  rewrite (mulrC (-1) mprat2).
  rewrite -mulrA.
  rewrite -mulrDr.
  rewrite mulN1r.
  done.
  intro.
  unlock pmul; simpl.
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

Lemma ple_sum {A} (c : seq A) (F1 F2 : A -> posrat) (f : A -> bool) :
  (forall x, f x -> F1 x <= F2 x) ->
  (\big[padd/0]_(p <- c | f p) F1 p) <= (\big[padd/0]_(p <- c | f p) F2 p).
  intros.
  induction c.
  rewrite !big_nil; done.
  rewrite !big_cons.
  remember (f a) as b; destruct b.
  apply ple_add_lr.
  apply H; rewrite -Heqb //=.
  done.
  done.
Qed.  

Lemma padd2 (a : posrat) :
  a + a = (Posrat 2%:Q is_true_true) * a.
  destruct a; apply/eqP; rewrite /eq_op //=; apply/eqP.
  have: intr 2 = (intr 1 + intr 1)%R.
  done.
  intro.
  unlock padd pmul; simpl.
  rewrite x.
  rewrite mulrDl.
  rewrite (mulrC (intr 1)).
  rewrite !mulr1z.
  rewrite mulr1.
  done.
Qed.

Lemma pinv_0 : pinv 0 = 0.
  simpl.
  apply/eqP; rewrite /eq_op //=.
  unlock pinv; simpl.
  rewrite invr0.
  done.
Qed.

Lemma pinv_neq0 a :
  a != 0 -> pinv a != 0.
  unlock pinv;
  destruct a; rewrite /pinv_; intro; rewrite /eq_op //=.
  apply invr_neq0.
  done.
Qed.

Definition pdiv_neq0 a b :
  a != 0 -> b != 0 -> a / b != 0.
  intros; rewrite -pmul0.
  rewrite negb_or.
  apply/andP; split.
  done.
  apply pinv_neq0; done.
Qed.


Definition pexp_neq0 a c :
  a != 0 -> (a ^+ c != 0).
  unlock pexp;
  destruct a; rewrite /pexp_; simpl.
  intro; rewrite /eq_op //=.
  apply expf_neq0.
  done.
Qed.

Definition pdiv_lt1 a b :
  b != 0 -> a < b -> a / b < 1.
  destruct a,b.
  unfold plt; simpl.
  intros.
  unlock pmul pinv; simpl.

  rewrite ltr_pdivr_mulr.
  rewrite mul1r. done.
  rewrite ltr_def.
  rewrite -Qnneg_def i0.
  rewrite /eq_op //= in H.
  rewrite H; done.
Qed.

Lemma pmul_div a b c d:
  (a / b) * (c / d) = (a * c) / (b * d).
  unlock pmul pinv; simpl.
  destruct a,b,c,d; apply/eqP; rewrite /eq_op //=; apply/eqP.
  apply mulf_div.
Qed.


Lemma pinv_1 :
  pinv 1 = 1.
  unlock pinv.
  rewrite /pinv.
  apply/eqP; rewrite /eq_op //=; apply/eqP.
Qed.

Lemma pdiv_pmul_num a b c :
  (a * b) / c = a * (b / c).
  rewrite -(pmul1r c).
  rewrite -pmul_div.
  rewrite pinv_1.
  rewrite pmulr1.
  rewrite pmul1r.
  done.
Qed.

Lemma pdiv_pmul_denom a b c:
  a / (b * c) = a / b * (1 / c).
  rewrite pmul_div.
  rewrite pmulr1.
  done.
Qed.

  Lemma psum_neq0 {A : eqType} (xs : seq A) f :
    (\big[padd/0]_(x <- xs) f x != 0) = (has (fun x => f x != 0) xs). 
    induction xs.
    rewrite big_nil //=.
    rewrite big_cons //=.
    rewrite -IHxs.
    apply Bool.eq_true_iff_eq; split.
    rewrite -padd0 negb_and; move/orP; elim => H; rewrite H //= ?orbT //=.

    move/orP; elim => H.
    rewrite -padd0 negb_and H //=.
    rewrite -padd0 negb_and H //= orbT //=.
  Qed.


  Lemma psum_eq0 {A : eqType} (xs : seq A) f :
    (\big[padd/0]_(x <- xs) f x == 0) = (all (fun x => f x == 0) xs). 
    induction xs.
    rewrite big_nil //=.
    rewrite big_cons //=.
    rewrite -IHxs.
    rewrite padd0; done.
  Qed.

Lemma pdivK (p : posrat) :
  p != 0 -> p / p = 1.
  move => H.
  destruct p; simpl in *; unlock pmul pinv; simpl.
  apply/eqP; rewrite /eq_op //=.
  rewrite GRing.Theory.divff.
  done.
  done.
Qed.

Lemma posrat_of_nat_0 :
  posrat_of_nat 0 = 0.
  unlock posrat_of_nat; simpl.
  apply/eqP; rewrite /eq_op //=.
Qed.

Lemma posrat_of_nat_neq0 n :
  posrat_of_nat (S n) != 0.
  unlock posrat_of_nat; simpl.
  rewrite /posrat_of_nat_; rewrite /eq_op //=.
  rewrite /intr //=.
  have: (0%R < n.+1%:R)%R.
  intro.
  apply ltr0Sn.
  intros.
  rewrite gtr_eqF.
  done.
  apply x.
Qed.

Lemma posrat_of_nat_S n :
  posrat_of_nat (S n) = 1 + posrat_of_nat n.
  unlock posrat_of_nat; simpl.
  rewrite /posrat_of_nat_.
  unlock padd; simpl.
  apply/eqP; rewrite /eq_op //=.
  rewrite /intr //=.
  have -> : (n.+1) = (1 + n)%N.
  done.
  rewrite natrD.
  apply/eqP; congr (_ + _)%R.
Qed.

Lemma iter_padd (n : nat) (p1 p2 : posrat) :
  iter n (padd p1) p2 =
  p2 + (posrat_of_nat n * p1).
  induction n.
  simpl.
  rewrite posrat_of_nat_0 pmul0r paddr0 //=.
  simpl.
  rewrite IHn.
  rewrite posrat_of_nat_S.
  rewrite pmulrDl pmul1r !paddrA.
  congr (_ + _).
  rewrite paddrC //=.
Qed.