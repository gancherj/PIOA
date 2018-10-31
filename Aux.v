
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Local Open Scope fset.


Definition all_fset {A : choiceType} (f : {fset A}) (p : A -> bool) : bool :=
  [fset x in f | p x] == f.

Lemma all_fsetP {A : choiceType} (f : {fset A}) (p : A -> bool) :
  reflect (forall (x : A), x \in f -> p x) (all_fset f p).
  apply: (iffP idP); rewrite /all_fset.
  move/eqP/fsetP => H x.
  move: (H x); rewrite !in_fset inE //=.
  destruct (x \in f).
  move/andP; elim; done.
  done.
  intro H; apply/eqP/fsetP => x.
  remember (x \in f) as b; symmetry in Heqb; destruct b.
  rewrite !in_fset !inE //= Heqb (H _ Heqb) //=.
  rewrite !in_fset !inE //= Heqb //=.
Qed.

Definition cover {A : choiceType} (f : {fset {fset A}}) : {fset A} :=
  \bigcup_(p <- f) p.

Lemma cover1 {A : choiceType} (f : {fset A}) :
  cover (fset1 f) = f.
    rewrite /cover big_seq_fset1 //=.
Qed.

Definition fpick {A : choiceType} (f : {fset A}) (b : A -> bool) : option A :=
  match (Sumbool.sumbool_of_bool ([fset x in f | b x] != fset0)) with
    | left Hin => Some (xchoose (fset0Pn _ Hin))
    | _ => None
             end.

Lemma fpickPt {A : choiceType} (f : {fset A}) b x :
  fpick f b = Some x -> b x /\ x \in f.
rewrite /fpick.
case: (Sumbool.sumbool_of_bool ([fset x0 | x0 in f & b x0] != fset0)) => H.
move => Heq; injection Heq => <-.
have H2 := (xchooseP (fset0Pn _ H)).
rewrite !in_fset !inE in H2.
move/andP: H2; elim; done.
done.
Qed.

Lemma fpickPn {A : choiceType} (f : {fset A}) b :
  fpick f b = None -> all_fset f (fun x => ~~ b x).
rewrite /fpick.
case: (Sumbool.sumbool_of_bool ([fset x0 | x0 in f & b x0] != fset0)) => H.
done.
move => _.
move: H.
move/negbFE/eqP/fsetP=>H.
apply/all_fsetP => x Hx.
move: (H x); rewrite !in_fset !inE //=.
rewrite Hx  andTb => -> //=.
Qed.

Inductive fpick_spec {A : choiceType} (f : {fset A}) b :=
  | fpick_true : forall x, fpick f b = Some x -> x \in f -> b x -> fpick_spec f b
  | fpick_false : fpick f b = None -> all_fset f (fun x => ~~ b x) -> fpick_spec f b.

Lemma fpickP {A : choiceType} (f : {fset A}) b : fpick_spec f b.
  remember (fpick f b); symmetry in Heqo; destruct o.
  elim (fpickPt _ _ _ Heqo) => h1 h2; eapply fpick_true.
  apply Heqo.
  apply h2.
  done.
  eapply fpick_false; rewrite //=.
  apply fpickPn; rewrite //=.
Qed.

Lemma fpick_eqP {A : choiceType} (f : {fset A}) (b1 b2 : A -> bool) :
  b1 =1 b2 -> fpick f b1 = fpick f b2.
  move=> Hb. 
  rewrite /fpick.
  have: [fset x | x in f & b1 x] = [fset x | x in f & b2 x].
  apply/fsetP => x; rewrite !in_fset !inE //=.
  rewrite Hb //=.
  move => ->.
  done.
Qed.

