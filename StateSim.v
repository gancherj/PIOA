

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap.

Require Import PIOA Meas Posrat Aux FastEnum.


Section StateInj.
  
  Context {A : choiceType}.
  Context (P1 P2 : @PIOA A).
  Context (hc1 : closed P1).
  Context (hc2 : closed P2).

  Record StateInj (R : pQ P1 -> pQ P2) :=
    {
      siStart : R (start _) = (start _);
      siStep : forall T mu eta, T \in channels P1 -> isSubdist mu ->
          measMap mu (fun p => (R p.1, p.2)) = eta ->
          exists ts, all (fun x => x \in channels P2) ts /\
           measMap (appChan P1 T mu) (fun p => (R p.1, p.2)) =
                      runPIOA P2 ts eta 
      }.


  Lemma stateSimSound R : StateInj R -> @refinement _ P1 P2 hc1 hc2.
    case => h1 h2.
    move => ts Hts.

    have: exists ts', all (fun x => x \in channels P2) ts' /\
        measMap (runPIOA P1 ts (startTr P1)) (fun p => (R p.1, p.2)) = runPIOA P2 ts' (startTr P2).
    induction ts using last_ind.
    exists nil.
    split.
    done.

    rewrite //= /startTr //= measMap_ret; congr (ret _); rewrite //= h1 //=.

    rewrite all_rcons in Hts; move/andP: Hts => [Hx Hts].


    destruct (IHts Hts) as [ts' Hts'].

    have Hsd : isSubdist (runPIOA P1 ts (startTr P1)).
    apply runPIOA_subDist; rewrite //=.
    rewrite /startTr isSubdist_ret //=.
    destruct Hts' as [Hts'1 Hts'2].
    destruct (h2 _ _ _ Hx Hsd Hts'2) as [x0 Hx0].
    simpl in *.

    exists (ts' ++ x0).
    split.
    rewrite all_cat.
    destruct Hx0 as [Hx01 Hx02].
    rewrite Hx01 Hts'1 //=.
    rewrite runPIOA_app runPIOA_rcons //=.
    destruct Hx0; rewrite //=.

    elim => ts' Hts'.
    exists ts'.
    destruct Hts'; split; rewrite //=.
    rewrite -H0.
    rewrite /traceOf measMap_measMap //=.
 Qed.
End StateInj.

Lemma runChan_conv_st {A} (P1 P2 : @PIOA A) (R : pQ P1 -> pQ P2) :
  (forall a s, omap (fun mu => measMap mu R) (tr P1 s a) = tr P2 (R s) a) ->
  (forall s, enabled P1 s =1 enabled P2 (R s)) ->
  (forall f s, omap (fun mua => (measMap mua.1 R, mua.2)) (runChan P1 f s) = (runChan P2 f (R s))).
  move => Tr_eq Henabled_eq f s.
  rewrite /runChan.
  rewrite -(fpick_eqP _ _ _ (Henabled_eq s)).
  case: (fpickP f (enabled P1 s)).
  move => x -> Hx Henabled.
  rewrite -Tr_eq.
  case (tr P1 s x) => [mu|]; rewrite //=.
  move => -> Hnenabled; rewrite //=.
Qed.

Section SimpleStateInj.
  
  Context {A : choiceType}.
  Context (P1 P2 : @PIOA A).
  Context (hc1 : closed P1).
  Context (hc2 : closed P2).

  Record SimpleStateInj (R : pQ P1 -> pQ P2) :=
  {
   _ : cI P1 = cI P2;
   _ : cO P1 = cO P2;
   _ : cH P1 = cH P2;
   _ : R (start P1) = start P2;
   _ : (forall a s, omap (fun mu => measMap mu R) (tr P1 s a) = tr P2 (R s) a);
  (* _ : (forall s, enabled P1 s =1 enabled P2 (R s)) *)
         }.

  Lemma simpleStateSound R : SimpleStateInj R -> @refinement _ P1 P2 hc1 hc2.
    move => ssi; eapply stateSimSound; instantiate (1 := R).
    destruct ssi.
    constructor; rewrite //=.
    move => C mu eta Ht Hsd Heq.
    exists (C :: nil); split; rewrite //=.
    apply/andP; split; rewrite //=.
    rewrite /channels //=.
    rewrite -H -H0 -H1 //=.

    rewrite /appChan measMap_bind -Heq measBind_measMap.
    apply measBind_eqP => x Hxin; rewrite //=.

    have: runChan P2 C (R x.1) = omap (fun mua => (measMap mua.1 R, mua.2)) (runChan P1 C x.1).
    rewrite /runChan.
    have: enabled P2 (R x.1) =1 enabled P1 x.1.
    rewrite /enabled //= => a; rewrite -H3. 
    remember (tr P1 x.1 a) as o; destruct o; rewrite -Heqo //=.

    move => Heqneq; rewrite (fpick_eqP _ _ _ Heqneq).
    case (fpickP C (enabled P1 x.1)). 
    move => a -> Ha Henabled; rewrite -H3.

    destruct (tr P1 x.1 a) ; rewrite //=.
    move => ->; rewrite //=.
    move => ->.

    remember (runChan P1 C x.1) as o; destruct o; rewrite -Heqo //=.
    destruct p; rewrite measMap_bind measBind_measMap //=; apply measBind_eqP => x0 Hx0.
    rewrite /hiddens H1.
    case (s \in cover (cH P2)); rewrite measMap_ret //=.
    rewrite measMap_ret //=.
  Qed.
End SimpleStateInj.