
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


Fixpoint lfind {A : eqType} (p : A -> bool) (xs : seq A) :=
  match xs with
  | nil => None
  | x :: xs' => if p x then Some x else lfind p xs'
                                                   end.

Inductive lfind_spec {A : eqType} (p : A -> bool) (xs : seq A) :=
  | lfind_some x : lfind p xs = Some x -> x \in xs -> p x -> lfind_spec p xs
  | lfind_none : lfind p xs = None -> all (fun x => ~~ p x) xs -> lfind_spec p xs.

Lemma lfindP {A : eqType} (p : A -> bool) xs : lfind_spec p xs.
  induction xs.
  apply lfind_none; rewrite //=.
  remember (p a) as b; symmetry in Heqb; destruct b.
  apply (lfind_some p (a :: xs) a); rewrite //=.
  rewrite Heqb //=.
  rewrite in_cons eq_refl orTb //=.
  destruct IHxs.
  apply (lfind_some p (a :: xs) x).
  rewrite //= Heqb //=.
  rewrite in_cons i orbT //=.
  done.
  apply lfind_none; rewrite //=.
  rewrite Heqb //= e //=.
  apply/andP; split.
  rewrite Heqb //=.
  done.
Qed.

Definition all_counter {A : eqType} (p : A -> bool) (xs : seq A) :=
  (lfind (fun x => ~~ p x) xs) == None .

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
  isSome (lfind (fun x => ~~ p x) xs) = ~~ (all p xs).
  rewrite all_counterP /all_counter //=.
  destruct (lfind (fun x => ~~ p x) xs); rewrite //=.
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
  
Definition opt_lift {A} (p : A -> bool) := fun (x : option A) =>
                                                 match x with
                                                   | Some a => p a
                                                   | None => true
                                                               end.

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

Lemma enum_orP b1 b2 :
  reflect ([\/ (b1 && ~~ b2), (b2 && ~~ b1) | (b1 && b2)]) (b1 || b2).
  apply/(iffP idP); destruct b1; destruct b2; rewrite //= => h.
  by apply Or33.
  by apply Or31.
  by apply Or32.
  elim h; done.
Qed.

Lemma catP {A : eqType} (s1 s2 : seq A) x :
  reflect ([\/ ((x \in s1) && (x \notin s2)), ((x \in s2) && (x \notin s1)) | ((x \in s1) && (x \in s2))])
          (x \in s1 ++ s2).
  apply/(iffP idP).
  rewrite mem_cat; move/enum_orP; done. 
  move/enum_orP; rewrite mem_cat //=.
Qed.

Notation "x <$>o f" := (omap f x) (at level 40).
Notation "x >>=o f" := (obind f x) (at level 40).

Lemma opt_neq_none {A : eqType} {x : option A} :
  reflect (exists a, x = Some a) (x != None).
  apply/(iffP idP); case x; rewrite //=.
  intros; exists s; done.
  elim; done.
Qed.

Lemma omap_eq_none {A B} (x : option A) (f : A -> B) :
  x = None <-> omap f x = None.
destruct x; done.
Qed.

Lemma omap_neq_none {A B : eqType} (x : option A) (f : A -> B) :
  (x != None) = (omap f x != None).
  destruct x; done.
Qed.

Lemma obind_eq_non {A B : eqType} (x : option A) (f : A -> option B) :
  reflect (x = None \/ (exists a, x = Some a /\ f a = None)) (obind f x == None).
  apply/(iffP idP).
  case x; rewrite //=.
  move => a; remember (f a) as fa. 
  move => hfa; right; exists a; rewrite -Heqfa (eqP hfa) //=. 
  move => _; left; done.
  elim.
  move => ->; done.
  elim => a; elim => -> h2 //=; apply/eqP; done.
Qed.

Lemma obind_neq_none {A B : eqType} (x : option A) (f : A -> option B) :
  reflect (exists a b, x = Some a /\ f a = Some b) (obind f x != None).
  apply/(iffP idP).
  case x; rewrite //=.
  move => a; remember (f a) as fa; destruct fa; rewrite //=.
  move => _; exists a, s; done.
  elim => a; elim => b; elim => h1 h2.
  rewrite h1 //=; rewrite h2 //=.
Qed.

Lemma obind_eq_some {A B : eqType} (x : option A) (f : A -> option B) b :
  reflect (exists a, x = Some a /\ f a = Some b) (obind f x == Some b).
  apply/(iffP idP).
  case x; rewrite //=.
  move => a; remember (f a) as fa; destruct fa; rewrite //=.
  move/eqP => heq; injection heq => <-.
  exists a; done.
  elim => a; elim => ->; rewrite //=  => ->; rewrite //=.
Qed.

(* sequence stuff *)

Definition seq_disjoint {A : eqType} (xs ys : seq A) :=
  all (fun x => all (fun y => x != y) ys) xs.

Lemma seq_disjoint_sym {A : eqType} (xs ys : seq A) :
  seq_disjoint xs ys = seq_disjoint ys xs.
  apply Bool.eq_true_iff_eq; split;
  move/allP => H; apply/allP => x Hx; apply/allP => y Hy.
  move/allP: (H _ Hy);move/(_ _ Hx); rewrite eq_sym //=.
  move/allP: (H _ Hy);move/(_ _ Hx); rewrite eq_sym //=.
Qed.

Lemma notin_seq_all {A : eqType} (x : A) xs :
  (x \notin xs) = (all (fun z => x != z) xs).
  induction xs; rewrite //= in_cons negb_or IHxs //=. 
Qed.

Lemma in_seq_has {A : eqType} (x : A) xs :
  (x \in xs) = (has (fun z => x == z) xs).
  induction xs; rewrite //=.
  rewrite in_cons IHxs.
  done.
Qed.

Lemma seq_disjointP {A : eqType} (xs ys : seq A) :
  reflect (forall x, x \in xs -> x \notin ys) (seq_disjoint xs ys).
apply/(iffP idP).
move/allP => H x Hx.
rewrite notin_seq_all; apply H; done.

move => H; apply/allP => x Hx; apply/allP => y Hy.
have H2 := H _ Hx; rewrite notin_seq_all in H2; move/allP: H2; move/(_ _ Hy); done.
Qed.

Definition seq_eqmem_dec {A : eqType} (xs ys : seq A) :=
  all (fun x => x \in ys) xs && all (fun y => y \in xs) ys.

Notation "A ==i B" := (seq_eqmem_dec A B) (at level 70).
Notation "A =/i B" := (~~ (A ==i B)) (at level 70).

Lemma seq_eqmemP {A : eqType} (xs ys : seq A) :
  reflect (xs =i ys) (xs ==i ys).
  apply/(iffP idP).
  move/andP; elim.
  move/allP => H1.
  move/allP => H2.
  move => x.
  remember (x \in xs) as b; destruct b; symmetry in Heqb.
  rewrite (H1 _ Heqb); done.
  remember (x \in ys) as b'; destruct b'; symmetry in Heqb'.
  rewrite (H2 _ Heqb') in Heqb; done.
  done.
  move=> H; apply/andP; split.
  apply/allP => x Hx.
  rewrite -H; done.
  apply/allP => X Hx; rewrite H; done.
Qed.

Definition seqD {A : eqType} (xs ys : seq A) :=
  foldr (fun a acc => if a \in ys then acc else a :: acc) nil xs.

Lemma seqDP {A : eqType} (xs ys : seq A) x :
  reflect (x \in xs /\ x \notin ys) (x \in seqD xs ys).
  apply/(iffP idP); induction xs; rewrite //=.
  remember (a \in ys) as b; destruct b; symmetry in Heqb.
  move/IHxs; elim; intros; split.
  rewrite in_cons H orbT //=.
  done.
  rewrite in_cons; move/orP; elim.
  move/eqP => ->.
  split; [rewrite in_cons eq_refl //= | rewrite Heqb //=].
  move/IHxs; elim; intros; split.
  rewrite in_cons H orbT //=.
  done.
  elim; rewrite in_nil //=.

  rewrite in_cons; elim.
  move/orP; elim.
  move/eqP => -> => H.
  remember (a \in ys) as b; destruct b; symmetry in Heqb.
  done.
  rewrite in_cons eq_refl orTb //=.
  intros; destruct (a \in ys).
  apply IHxs; split; done.
  rewrite in_cons IHxs ?orbT //=.
Qed.


Lemma seqD_eqnil {A : eqType} (xs ys : seq A) :
  reflect (forall x, x \in xs -> x \in ys) (seqD xs ys ==  nil).
  apply/(iffP idP).
  induction xs; rewrite //=.
  remember (a \in ys) as b; destruct b.
  move/IHxs => h1 h2.
  rewrite in_cons; move/orP; elim.
  move/eqP => ->; done.
  intros; apply h1; done.
  done.

  move => H; induction xs; rewrite //=.
  remember (a \in ys) as b; destruct b.
  apply IHxs.
  move => x hx; apply H.
  rewrite in_cons hx orbT //=.
  rewrite H in Heqb.
  done.
  rewrite in_cons eq_refl //=.
Qed.

Lemma mem_seqD {A : eqType} (xs ys : seq A) x :
  (x \in seqD xs ys) = ((x \in xs) && (x \notin ys)) .
  apply Bool.eq_true_iff_eq; split => H.
  elim (seqDP _ _ _ H) => -> -> //=.
  apply/seqDP; split; elim (andP H); done.
Qed.