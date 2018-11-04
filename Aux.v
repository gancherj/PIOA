
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Local Open Scope fset.


Definition all_fset {A : choiceType}  (p : A -> bool) f : bool :=
  [fset x in f | p x] == f.

Lemma all_fsetP {A : choiceType} (f : {fset A}) (p : A -> bool) :
  reflect (forall (x : A), x \in f -> p x) (all_fset p f).
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

Lemma all_fset0 {A : choiceType} (p : A -> bool) :
  all_fset p fset0 = true.
  apply/all_fsetP; rewrite //=.
Qed.

Lemma all_fset1 {A : choiceType} (x : A) p :
  all_fset p [fset x] = p x.
  remember (p x) as b; destruct b.
  apply/all_fsetP => y Hy.
  rewrite in_fset1 in Hy; rewrite (eqP Hy); done.
  apply negbTE; apply/contraT; rewrite negbK; move/all_fsetP => H.
  have: p x.
  apply H; rewrite in_fset1 eq_refl //=.
  rewrite -Heqb //=.
Qed.

Lemma all_fsetU {A : choiceType} (f g : {fset A}) p :
  all_fset p (f `|` g) = all_fset p f && all_fset p g.
  apply Bool.eq_true_iff_eq; split.
  move/all_fsetP => H; apply/andP; split; apply/all_fsetP => x Hx; apply H; apply/fsetUP; [left |right]; done.
  move/andP; elim; move/all_fsetP => H1; move/all_fsetP => H2; apply/all_fsetP => x Hx; move/fsetUP: Hx; elim; [apply H1 | apply H2].
Qed.

Definition cover {A : choiceType} (f : {fset {fset A}}) : {fset A} :=
  \bigcup_(p <- f) p.

Lemma cover1 {A : choiceType} (f : {fset A}) :
  cover (fset1 f) = f.
    rewrite /cover big_seq_fset1 //=.
Qed.

Lemma coverU {A : choiceType} (f g : {fset {fset A}}) :
  cover f `|` cover g = cover (f `|` g).
  rewrite /cover; apply/fsetP => x; apply Bool.eq_true_iff_eq; split.
  move/fsetUP; elim; move/bigfcupP; elim => y Hy1 Hy2; apply/bigfcupP; eexists.
  rewrite andbT; apply/fsetUP; left; rewrite andbT in Hy1; apply Hy1. done.
  rewrite andbT; apply/fsetUP; right; rewrite andbT in Hy1; apply Hy1. done.
  move/bigfcupP; elim => y Hy1 Hy2.
  rewrite andbT in Hy1; move/fsetUP: Hy1; elim => H; apply/fsetUP.
  left; apply/bigfcupP; exists y.
  rewrite andbT; done.
  done.
  right; apply/bigfcupP; exists y.
  rewrite andbT; done.
  done.
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
  fpick f b = None -> all_fset (fun x => ~~ b x) f.
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
  | fpick_false : fpick f b = None -> all_fset (fun x => ~~ b x) f -> fpick_spec f b.

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


Definition fset_of_seq {A : choiceType} (s : seq A) :=
  foldr (fun a acc => a |` acc)%fset fset0 s.

Lemma fset_of_seq_cons {A : choiceType} (s : seq A) x :
  fset_of_seq (x :: s) = (x |` fset_of_seq s)%fset.
    rewrite /fset_of_seq //=.
Qed.    

Lemma fset_of_seq_cat {A : choiceType} (s1 s2 : seq A)  :
  fset_of_seq (s1 ++ s2) = (fset_of_seq s1 `|` fset_of_seq s2)%fset.
  move: s2.
  induction s1 => s2; rewrite //=.
  rewrite fset0U //=.
  rewrite IHs1.
  rewrite fsetUA //=.
Qed.

Lemma all_fset_all {A : choiceType} (s : seq A) (p : A -> bool) :
  all p s = all_fset p (fset_of_seq s) .
  induction s; rewrite //=.
  symmetry; apply/all_fsetP; rewrite //=.
  rewrite IHs all_fsetU; congr (_ && _).
  rewrite all_fset1 //=.
Qed.

Lemma in_fset_of_seq {A : choiceType} (s : seq A) x :
  (x \in s) = (x \in fset_of_seq s). 
  induction s; rewrite //=.
  rewrite in_cons in_fsetU in_fset1 IHs //=.
Qed.

Lemma all_flatten {A} (s : seq (seq A)) P :
  all P (flatten s) = all (all P) s.
  induction s; rewrite //=.
  rewrite all_cat IHs //=.
Qed.  

Lemma all_fset_cover {A : choiceType} (s : {fset {fset A}}) (P : A -> bool) :
  all_fset P (cover s) = @all_fset [choiceType of {fset A}] (fun c => all_fset P c) s.
  apply Bool.eq_true_iff_eq; split; move/all_fsetP => H; apply/all_fsetP => x Hx.
  apply/all_fsetP => y Hy.
  apply H.
  apply/bigfcupP; exists x.
  rewrite andbT //=.
  done.
  elim (bigfcupP _ _ _ _ Hx) => y Hy1 Hy2.
  rewrite andbT in Hy1.

  move/all_fsetP: (H y Hy1).
  move/(_ _ Hy2); done.
Qed.

Lemma fset_of_seq_flatten {A : choiceType} (s : seq (seq A)) :
  fset_of_seq (flatten s) = cover (fset_of_seq (map fset_of_seq s)).
  apply/fsetP => x.
  rewrite -in_fset_of_seq.
  apply Bool.eq_true_iff_eq; split.
  move/flattenP; elim => y Hy1 Hy2.
  apply/bigfcupP; exists (fset_of_seq y).
  rewrite -in_fset_of_seq andbT; apply/mapP; exists y; done.
  rewrite -in_fset_of_seq //=.

  move/bigfcupP; elim => y Hy Hy2; apply/flattenP.
  rewrite andbT -in_fset_of_seq in Hy; elim (mapP Hy) => z Hz H'; subst; eexists.
  apply Hz.
  rewrite in_fset_of_seq //=.
Qed.


Fixpoint has_compute {A : eqType} (p : A -> bool) (xs : seq A) :=
  match xs with
  | nil => None
  | x :: xs' => if p x then Some x else has_compute p xs'
                                                   end.

Definition all_counter {A : eqType} (p : A -> bool) (xs : seq A) :=
  (has_compute (fun x => ~~ p x) xs) == None .

Lemma all_counter_cons {A : eqType} (p : A -> bool) xs x :
  all_counter p (x :: xs) = ((p x)) && all_counter p xs.
rewrite /all_counter //=.
destruct (p x); rewrite //=.
Qed.

Definition all_counterP {A : eqType} (p : A -> bool) xs :
  all p xs = all_counter p xs.
  induction xs; rewrite //=.
  rewrite all_counter_cons IHxs //=.
Qed.

Definition all_counterPn {A : eqType} (p : A -> bool) xs :
  isSome (has_compute (fun x => ~~ p x) xs) = ~~ (all p xs).
  rewrite all_counterP /all_counter //=.
  destruct (has_compute (fun x => ~~ p x) xs); rewrite //=.
Qed.

Lemma all_all {A B} (p : A -> B -> bool) xs ys :
  all (fun x => all (p x) ys) xs = all (fun x => p x.1 x.2) (allpairs (fun x y => (x,y)) xs ys).
  induction xs; rewrite //=.
  rewrite all_cat IHxs.
  congr (_ && _).
  clear; induction ys; rewrite //=.
  rewrite IHys //=.
Qed.

Lemma all_imply_all {A B} (p1 : A -> bool) (p2 : A -> B -> bool) xs ys :
  all (fun x => p1 x ==> all (p2 x) ys) xs =
  all (fun x => (~~ p1 x.1) || (p1 x.1 && p2 x.1 x.2)) (allpairs (fun x y => (x, y)) xs ys).
  induction xs; rewrite //=.
  rewrite all_cat IHxs.
  congr (_ &&_ ).
  
  clear; induction ys; rewrite //=.
  destruct (p1 a); rewrite //=.
  rewrite -IHys.
  destruct (p1 a); destruct (p2 a a0); destruct (all (p2 a) ys); rewrite //=.
Qed.


Fixpoint multiIf {A} (cs : list (bool * A)) : option A :=
  match cs with
  | (true, a) :: _ => Some a
  | (false, _) :: xs => multiIf xs                           
  | nil => None
             end.
  
Fixpoint multiIf_with_posrec {A} n (cs : list (bool * A)) : option (nat * A) :=
  match cs with
  | (true, a) :: _ => Some (n, a)
  | (false, _) :: xs => multiIf_with_posrec (succn n) xs                           
  | nil => None
             end.

Definition multiIf_with_pos {A} (cs : list (bool * A)) := multiIf_with_posrec 0 cs.
  
Lemma multiIfP {A} (cs : list (bool * A)) (P : A -> bool) :
  all (fun x => P x.2) cs -> opt_lift P (multiIf cs).
  induction cs; rewrite //=.
  move/andP; elim => H1 H2.
  destruct a; rewrite //=.
  destruct b.
  done.
  apply IHcs; rewrite //=.
Qed.

Lemma multiIfPosE {A} (cs : list (bool * A)) :
  multiIf cs = omap snd (multiIf_with_pos cs).
  rewrite /multiIf_with_pos.
  move: 0.
  induction cs; rewrite //=.
  destruct a; destruct b; rewrite //=.
Qed.

Lemma all_cons {A} (xs : seq A) (x : A) (p : A -> bool) :
  p x -> all p xs -> all p (x :: xs).
  rewrite //= => H1 H2; apply/andP; split; done.
Qed.

Ltac split_all :=
  match goal with
  | [ |- is_true (all _ (_ :: _))] => apply all_cons; [idtac | split_all]

  | [ |- is_true (all _ nil)] => rewrite all_nil //=
                               end. 

Lemma omap_eq_some {A B} (x : option A) (f : A -> B) :
  x = None <-> omap f x = None.
destruct x; done.
Qed.