From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

From Template Require Import monad_utils Ast Loader All.
Import MonadNotation.

Set Primitive Projections.

(* info and getFields come from coq-lens *)


Local Definition getRecordFields (mi : mutual_inductive_body) (n : nat)
: TemplateMonad (list (ident * term)) :=
  match nth_error mi.(ind_bodies) n with
  | None => tmFail "no body for index"
  | Some oib =>
    match oib.(ind_ctors) with
    | nil => tmFail "`getFields` got empty type"
    | ctor :: nil =>
      ret (oib.(ind_projs))
    | _ => tmFail "`getFields` got variant type"
    end
  end.




    



Fixpoint mmwi_aux {A} {B} (f : nat -> A -> TemplateMonad B) (xs : list A) (i : nat) (acc : list B) :=
  match xs with
    | x :: xs' => a <- f i x ;; mmwi_aux f xs' (S i) (acc ++ (a :: nil))
    | nil => ret acc
                 end.

Fixpoint monad_map_with_index {A} {B} (f : nat -> A -> TemplateMonad B) (xs : list A) : TemplateMonad (list B) :=
  mmwi_aux f xs 0 nil.

Definition perFieldOfRecord (T : Type) {A} (f : term -> inductive -> nat -> ident * term -> TemplateMonad A) : TemplateMonad (list A) :=
  tyT <- tmQuote T ;;
  match tyT with
  | tInd i _ =>
    let name := i.(inductive_mind) in
    ind <- tmQuoteInductive name ;;
    info <- getRecordFields ind i.(inductive_ind) ;;
    monad_map_with_index (fun n it => f tyT i n it) (info)
  | _ => tmFail "given type not inductive"
    end.

Definition typesInRecord (T : Type) :=
  perFieldOfRecord T (fun _ _ _ it => ret (snd it)).

Definition printTerm {T} (x : T) := tmQuote x >>= tmEval cbv >>= tmPrint.

Quote Definition tpair := @pair.
Quote Definition tprod := prod.

(* given a list of terms, make the right-associated elments of the pair *)
Fixpoint mkMultiPair_aux (ts : list (term * term)) (* type * value *) : TemplateMonad ((term * term) * (term * term)) :=
  match ts with
    | nil => tmFail "null input to mkMultiPair"
    | x :: nil => tmFail "only one input to mkMultiPair"
    | x :: y :: nil => ret (x, y)
    | x :: xs => 
      p <- mkMultiPair_aux xs ;;
      let tr_typ :=
            tApp tprod (fst (fst p) :: fst (snd p) :: nil)
      in
      let tr_val :=
          tApp tpair (fst (fst p) :: fst (snd p) :: snd (fst p) :: snd (snd p) :: nil) in
      ret (x, (tr_typ, tr_val))
         end.

Definition mkMultiPair ts :=
  p <- mkMultiPair_aux ts ;;
  ret (tApp tpair (fst (fst p) :: fst (snd p) :: snd (fst p) :: snd (snd p) :: nil)).

Definition record_to_pairs (T : Type) :=
  ts <- perFieldOfRecord T (fun tm ind i nt =>
                                   ret (snd nt, tProj (ind, 0, i) (tRel 0))) ;;
  x <- mkMultiPair ts ;; 
  x <- tmEval cbv x ;;
  ty <- tmQuote T ;;
  tmEval cbv (tLambda (nAnon) ty x).

Definition record_to_pairs_type (T : Type) :=
  ts <- perFieldOfRecord T (fun tm ind i nt =>
                              ret (snd nt, tProj (ind, 0, i) (tRel 0))) ;;
  p <- mkMultiPair_aux ts ;;
  ret (tApp tprod (fst (fst p) :: fst (snd p) :: nil)).
     


Definition numRecordElems (T : Type) : TemplateMonad nat :=
  t <- perFieldOfRecord T (fun _ _ _ _ => ret tt) ;;
  tmEval cbv (Datatypes.length t).

Quote Definition tfst := @fst.
Quote Definition tsnd := @snd.

Check (fun x => fst (fst x)).

Definition types_in_prod (t : term) : TemplateMonad (option (term * term)):=
  match t with
    | tApp _ (x :: y :: nil) => ret (Some ((x, y)))
    | _ => ret None
                  end.

Definition fst_or_id (t : term * term) : TemplateMonad (term * term) :=
  res <- types_in_prod (fst t) ;;
  match res with
        | Some (t1, t2) => 
            ret (t1, tApp tfst (t1 :: t2 :: snd t :: nil))
        | None => ret t
        end.

Definition snd_or_fail (t : term * term) : TemplateMonad (term * term) :=
  res <- types_in_prod (fst t) ;;
  match res with
        | Some (t1, t2) => 
            ret (t2, tApp tsnd (t1 :: t2 :: snd t :: nil))
        | None => tmFail "bad snd"
        end.

Definition head_fail {A} (x : list A) : TemplateMonad A:=
  match x with
    | x :: xs => ret x
    | nil => tmFail "bad list"
                    end.

Fixpoint por_aux (tm : term * term) (i : nat) {struct i} : TemplateMonad (list (term * term)) :=
  match i with
    | 0 => ret (tm :: nil)
    | S n =>
      (p <- por_aux tm n ;;
      hd <- head_fail p ;;
      t1 <- snd_or_fail hd ;;
      ret (t1 :: p))
      end.

Fixpoint last_of_pairs (fuel : nat) (tm : term * term) : TemplateMonad (term * term) :=
  match fuel with
    | 0 => ret tm
    | S f => 
    t <- types_in_prod (fst tm) ;;
    match t with
        | Some _ => t' <- snd_or_fail tm ;; last_of_pairs f t'
        | None => ret tm
                    end end.

Fixpoint projs_of_rassc_list (T : Type) (tm : term * term) : TemplateMonad (list term) :=
  i <- numRecordElems T ;;
  ls <- por_aux tm (Nat.sub i 2) ;;
  e1 <- monad_map
    (fun t =>
       fst_or_id t) ls ;;
  e2 <- last_of_pairs (Nat.sub i 1) tm ;;
  ret (map snd (rev (e2 :: e1))).
    
(* construct of record. index is always 0 because there is only one variant *)
Definition construct_of_tind (t : term) : TemplateMonad term :=
  match t with
    | tInd ind ui => ret (tConstruct ind 0 ui)
    | _ => tmFail "bad input to construct_of_tind"
                  end.

Definition pairs_to_record (T : Type)  : TemplateMonad term :=
  let x := tRel 0 in
  tyT <- tmQuote T ;;
  constr <- construct_of_tind tyT ;;
  y <- record_to_pairs_type T ;;
  bs <- projs_of_rassc_list T (y, x) ;;
  body <- tmEval cbv (tApp constr bs) ;;
  tmEval cbv (tLambda (nNamed "x") y body) .


(* classes for finding resolution *)

Class eq_class (T : Type) := EqClass { _et : eqType }.
Instance find_eq_class (e : eqType) : eq_class e := EqClass e e.
Definition get_eq_class (T : Type) `{eq_class T} := _et.

Class choice_class (T : Type) := ChoiceClass { _ct : choiceType }.
Instance find_choice_class (e : choiceType) : choice_class e := ChoiceClass e e.
Definition get_choice_class (T : Type) `{choice_class T} := _ct.

Class count_class (T : Type) := CountClass { _ctt : countType }.
Instance find_count_class (e : countType) : count_class e := CountClass e e.
Definition get_count_class (T : Type) `{count_class T} := _ctt.

Class fin_class (T : Type) := FinClass { _ft : finType }.
Instance find_fin_class (e : finType) : fin_class e := FinClass e e.
Definition get_fin_class (T : Type) `{fin_class T} := _ft.


(* below I need a templatemonad function which on input T, outputs the choiceType for T if one exists, else none. Similarly for finType, .. *)


Definition tmFindEqtype (T : Type) : TemplateMonad (eqType) :=
  oi <- tmInferInstance (eq_class T) ;;
     match oi return TemplateMonad eqType with
     | Some inst =>
       ret ((@_et _ inst))
     | None => tmFail "cannot find eqtype"
                   end.

Definition tmFindChoicetype (T : Type) : TemplateMonad (choiceType) :=
  oi <- tmInferInstance (choice_class T) ;;
     match oi with
     | Some inst =>
       ret ((@_ct _ inst))
     | None => tmFail "cannot find choicetype"
                   end.

Definition tmFindCountType (T : Type) : TemplateMonad (countType) :=
  oi <- tmInferInstance (count_class T) ;;
     match oi with
     | Some inst =>
       ret ((@_ctt _ inst))
     | None => tmFail "cannot find countType"
                   end.

Definition tmFindFinType (T : Type) : TemplateMonad (finType) :=
  oi <- tmInferInstance (fin_class T) ;;
     match oi return TemplateMonad finType with
     | Some inst =>
       ret ((@_ft _ inst))
     | None => tmFail "cannot find choicetype"
                   end.

Definition tmCast {T : Type} (x : T) (T' : Type) :=
  t <- tmQuote x ;;
  tmUnquoteTyped T' t.

Definition mkEq (T : Type) (e : eqType) (f : T -> e) (g : e -> T) (H : cancel f g) :=
  EqType T (CanEqMixin H).

Definition registerEq (T : Type) (E : Type) (f : T -> E) (g : E -> T) (H : cancel f g) : TemplateMonad (Equality.mixin_of T) :=
  eqt <- tmFindEqtype E ;;
    f' <- tmCast f (T -> Equality.sort eqt) ;;
    g' <- tmCast g (Equality.sort eqt -> T) ;;
    H' <- tmCast H (cancel f' g') ;;
    n <- tmFreshName "gen_eqt" ;;
    q <- tmQuote (EqType T (CanEqMixin H')) ;;
    tmMkCanonical n q ;;
    ret (CanEqMixin H').

Definition cheat_phantid {T1 T2 : Type} (x : T1) (y : T2) : @phant_id T1 T2 x y.
move => a.
apply Phantom.
Defined.

Definition registerChoice (T : Type) (E : Type) (f : T -> E) (g : E -> T) (H : cancel f g) (eqm : Equality.mixin_of T) : TemplateMonad (Choice.class_of T) :=
  eqt <- tmFindEqtype T ;;
  ct <- tmFindChoicetype E ;;
  et_e <- tmFindEqtype E ;;
    f'' <- tmCast f (T -> Equality.sort et_e) ;;
    g'' <- tmCast g (Equality.sort et_e -> T) ;;
    H'' <- tmCast H (cancel f'' g'') ;;
  let teq := mkEq T et_e f'' g'' H'' in
    f' <- tmCast f (Equality.sort teq -> Choice.sort ct) ;;
    g' <- tmCast g (Choice.sort ct -> Equality.sort teq) ;;
    H' <- tmCast H (cancel f' g') ;;
    n <- tmFreshName "gen_choice" ;;
    q <- tmQuote (@Choice.pack T (CanChoiceMixin H') eqm eqt (cheat_phantid _ _)) ;;
    tmMkCanonical n q ;;
    cl <- tmFindChoicetype T ;;
    tmCast (Choice.class cl) (Choice.class_of T).

Definition registerCount (T : Type) (E : Type) (f : T -> E) (g : E -> T) (H : cancel f g) : TemplateMonad unit :=
  n <- tmFreshName "gen_count" ;;
  ct_t <- tmFindChoicetype T ;;
  ct_e <- tmFindCountType E ;;
  f' <- tmCast f (T -> Countable.sort ct_e) ;;
  g' <- tmCast g (Countable.sort ct_e -> T) ;;
  H' <- tmCast H (cancel f' g') ;;
  b <- tmCast (Choice.class ct_t) (Choice.class_of T) ;; 
  q <- tmQuote (@Countable.pack T (CanCountMixin H') ct_t b (cheat_phantid _ _));; 
  tmMkCanonical n q ;; 
  ret tt.

Definition registerFin (T : Type) (E : Type) (f : T -> E) (g : E -> T) (H : cancel f g) (eqmix_t : Equality.mixin_of T) : TemplateMonad unit :=
  n <- tmFreshName "gen_fin" ;;
  ct_t <- tmFindChoicetype T ;;
  b <- tmCast (Choice.class ct_t) (Choice.class_of T) ;;
  count_t <- tmFindCountType T ;;
  ft_e <- tmFindFinType E ;;
  f' <- tmCast f (Countable.sort count_t -> Finite.sort ft_e) ;;
  g' <- tmCast g (Finite.sort ft_e -> Countable.sort count_t) ;;
  H' <- tmCast H (cancel f' g') ;;
  let mix := @CanFinMixin count_t ft_e f' g' H' in
  mix' <- tmCast mix (@Finite.mixin_of (@Equality.Pack T (@Choice.base T b) T)) ;; 
  let fcl := @Finite.Class T b mix' in
  let ty := @Finite.Pack T fcl T in
  q <- tmQuote ty ;;
  tmMkCanonical n q.
    

(* Derive fin from a record with at least two elements; each part of record must already have fintype instance *)
Definition deriveFinRecord (T : Type) (nf ng nH1 nH2 : ident)  : TemplateMonad unit :=
  tpairs <- record_to_pairs_type T ;;
  pairs <- tmUnquoteTyped Type tpairs ;;
  tf <- record_to_pairs T ;;
  f <- tmUnquoteTyped (T -> pairs) tf ;;
  tg <- pairs_to_record T ;;
  g <- tmUnquoteTyped (pairs -> T) tg ;;
  nH1' <- tmFreshName nH1 ;;
  Hcan <- tmLemma nH1' (cancel f g) ;;
  eqmix <- registerEq T pairs f g Hcan ;;
  cl <- registerChoice T pairs f g Hcan eqmix ;;
  t_choice <- tmFindChoicetype T ;;
  registerCount T pairs f g Hcan ;;
  registerFin T pairs f g Hcan eqmix ;;
  nf' <- tmFreshName nf ;;
  tmMkDefinition nf' tf ;;
  ng' <- tmFreshName ng ;;
  tmMkDefinition ng' tg ;;
  nH2' <- tmFreshName nH2 ;;
  l2 <- tmLemma nH2 (cancel g f) ;;
  ret tt.

(* inductives *)

(* simple inductive *)
(* SIInfo: list of ctrs and their types in order *)
Definition SIInfo := list (list term).
    
Quote Definition tunit := unit.

Fixpoint strip_last_from_ctor (t : term) :=
  match t with
  | tProd n t1 t2 =>
    match t2 with
      | tRel _ => strip_last_from_ctor t1 
      | _ => tProd n t1 (strip_last_from_ctor t2)
    end
  | tRel _ => tunit 
  | _ => t end.

Definition getVariantConstrs (mi : mutual_inductive_body) : TemplateMonad (list term) :=
  match head mi.(ind_bodies) with
  | Some oib =>
    match oib.(ind_ctors) with
    | xs => ret (map (fun p => strip_last_from_ctor p.1.2) xs)
    end
  | None => tmFail "bad input"
      end.


(* returns list of terms of constructor arguments. *)
Definition iinfo (T : Type) :=
  tyT <- tmQuote T ;;
      match tyT with
      | tInd i _ =>
        let name := i.(inductive_mind) in
        ind <- tmQuoteInductive name ;;
        getVariantConstrs ind
      | _ => tmFail ""
                    end.


Quote Definition tsum := sum.
Fixpoint termlist_to_options_type (t : list term) : TemplateMonad term :=
  match t return TemplateMonad term with
    | x :: nil => ret x
    | nil => tmFail "bad input"
    | x :: zs =>
      x' <- termlist_to_options_type (zs) ;;
      ret (tApp tsum (x :: x' :: nil))
             end.

(* tCase: ind (fun to type) (thing im doing case on) (list of (num args * body of arm) *)
Fixpoint expand_prods (t : term) : list term :=
  match t with
  | tApp tsum (ty1 :: ty2 :: nil) =>
    (expand_prods ty1) ++ (expand_prods ty2)
  | _ => [:: t]
           end.


Fixpoint addIndices (ts : list term) (n : nat) :=
  match ts with
    | x :: xs => (x, n) :: addIndices xs n
    | nil => nil end.

Definition doCase (ts : list term) : TemplateMonad term := mkMultiPair (map (fun p => (p.1, tRel p.2)) (addIndices ts 0)).

Fixpoint handleLambdas (ts2 : list term) (ts : list term) : TemplateMonad term :=
  match ts with
  | t :: ts =>
    handleLambdas (t :: ts) ts >>= fun a => ret (tLambda nAnon t a)
  | nil => doCase ts2
                  end.
  
  

      


