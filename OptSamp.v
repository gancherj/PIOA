
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint finmap.

Require Import Meas Aux PIOA Ascii String CompPIOA SSRString FastEnum Action Refinement Compute PIOAOps StateSim.

Require Import Coq.Strings.String Closure. 
Local Open Scope string_scope.
Import zmodp.

Require Import Lens.Lens Lens.TC.

Require Import Derive.


Set Primitive Projections.

(* 
 x <- gen
 i <- adv
 out x + i


vs

 x <- gen
 i <- adv
 out x
*)

Section OIDef.
  Context (T : finType) (HT : 0 < #|T|).
  Context (f : T -> T -> T) (Hf : forall x, bijective (f x)).

Definition OI_H :=
  mkCon [finType of unit] (fun _ => [finType of unit]).

(* false is input, true is output *)
Definition OI_V :=
  mkCon [finType of bool] (fun b => [finType of T]).

Definition oiSt := ((option T) * (option T))%type.

Definition compute_z (x : option T) (y : T) :=
  obind (fun a => 
          Some (f a y)%R) x.


Definition compute_o (x y : option T) :=
  obind (fun a =>
           obind (fun b =>
                    Some (f a b)) x) y.

Definition oi_trans (wh : bool) (s : oiSt) (a : action OI_H + action OI_V) : option {meas oiSt} :=
  match a with
  | inl _ =>
    if (s.1 == None) then
      Some (x <- munif ([finType of T]); ret (Some x, s.2))
           else None
  | inr (existT b msg) =>
    if (b == false) then (* input *)
      if (s.2 == None) then
        Some (
            ret (s.1, compute_z (s.1) msg))
      else
        Some (ret s)
    else (* output *)
      if (if wh then ((s.1 != None) && (s.2 == Some msg)) else compute_o s.1 s.2 == Some msg) then Some (ret s) else None
           end.

Definition OI_data (wh : bool) : PIOA_data OI_V OI_H.
  econstructor.
  apply ((None, None) : (option T) * (option T)).
  apply ([:: false]).
  apply ([:: true]).
  apply (oi_trans wh).
Defined.

Lemma OI_spec wh : PIOA_spec (OI_data wh).
  econstructor.
  done.
  done.
  intros.
  simpl in H.
  rewrite mem_seq1 in H; rewrite (eqP H) in H0, H1.
  simpl in *.
  rewrite if_neq_None in H0.
  rewrite if_neq_None in H1.
  have: Some m1 = Some m2.
  destruct wh.
  elim (andP H0) => _ h0.
  elim (andP H1) => _ h1.
  rewrite -(eqP h0) -(eqP h1) //=.
  rewrite -(eqP H0) -(eqP H1) //=.
  inj; done.


  simpl.
  move => s i; rewrite mem_seq1; move/eqP => -> //=.
  destruct s.2; rewrite //=.

  intro; case; case; case; simpl; intro; intro. 
  pioa_dist_tac.
  simpl.
  

  apply dist_bind.
  apply dist_munif.
  simpl.
  apply lt0n_neq0; apply/card_gt0P.
  move/card_gt0P: HT; elim => i Hi; exists i; done.
  intros; apply dist_ret.

  pioa_dist_tac.
  pioa_dist_tac.
Qed.

Definition OI1 := mkPIOA _ _ (OI_data false) (OI_spec false).
Definition OI2 := mkPIOA _ _ (OI_data true) (OI_spec true).

Lemma oi1_appv_true :
  forall s, app_v OI1 true s =
            match (compute_o s.1 s.2) with
            | Some a => ret (s, Some (mkact OI_V true a))
            | None => ret (s, None)
                          end.
  move => s; case: (app_vP OI1 true s).
  done.
  move => m mu.
  simpl.
  move/eqP.
  rewrite if_eq_Some.
  move/andP; elim => h1 h2.
  move => ->.
  rewrite -(eqP h2); rewrite measE.
  rewrite /compute_o in h1.
  move/obind_eq_some: h1; elim => x; elim => h3.
  move/eqP/obind_eq_some; elim => y; elim => h4 h5.
  injection h5 => <-.
  rewrite h3 h4; simpl.
  done.
  move => H ->.
  simpl.
  remember (compute_o s.1 s.2) as o; destruct o; rewrite -Heqo.
  move: (H (mkact (OI_V) true s0) is_true_true).
  rewrite /enabled if_neq_None -Heqo eq_refl; done.
  done.
Qed.

Lemma oi2_appv_true :
  forall s,
    app_v OI2 true s =
    match s.1, s.2 with
    | Some _, Some a => ret (s, Some (mkact OI_V true a))
    | _, _ => ret (s, None)
                     end.
  move => s; case: (app_vP OI2 true s); rewrite //=.
  move => m mu; move/eqP; rewrite if_eq_Some; move/andP; elim; move/andP; elim => h1 /eqP -> /eqP <-.
  move => ->.
  move/opt_neq_none: h1; elim => a Ha; rewrite Ha measE //=.

  move => h ->.
  caseOn (s.2 == None).
  move/eqP => ->.
  remember (s.1) as s0; destruct s0; rewrite -Heqs0; done.
  move/opt_neq_none; elim => x Hx; simpl.
  caseOn (s.1 == None).
  move/eqP => ->; done.
  move/opt_neq_none; elim => a Ha.
  move: (h (mkact OI_V true x) is_true_true).
  rewrite /enabled negbK; simpl; rewrite if_eq_None Hx eq_refl //=.
  rewrite andbT Ha; done.
Qed.

Check SimpleStateInj.

Definition OIR : oiSt -> oiSt :=
  fun x =>
    match x with
    | (None, None) => x
    | (Some a, None) => (Some a, None)
    | (Some a, Some b) => (Some (f a b), Some b)                           
    | (None, Some b) => x
             end.

Lemma OIRP :
  SimpleStateInj OI1 OI2 OIR.
  constructor.
  done.
  simpl => x c; rewrite mem_seq1; move/eqP => ->.
  rewrite oi1_appv_true.
  rewrite oi2_appv_true.
  destruct x as [[x0 |] [x1 |]]; simpl.
  rewrite measE; simpl.
  simpl
  
  rewrite !measE //=.
  


                                                                                       

Definition OIR : {meas oiSt} -> {meas oiSt} -> bool :=
  fun mu eta =>
  ((mu <$> oi_corr) == eta).

Lemma OIRstateRel :
  StateRel OI1 OI2 (fun c => (nil, c, nil))
           (fun h => (h :: nil))
           OIR.
  constructor.
  simpl.
  rewrite /OIR !measE //=.
  move => c mu eta t Hc.
  rewrite mem_seq1 in Hc; rewrite (eqP Hc) {Hc}.
  rewrite /OIR; move/eqP => <-.
  simpl.
  rewrite !measE; munder (rewrite measE).
  apply closure_bind => x Hx.
  rewrite -oi_corrP measE.
  case: (app_vP OI1 true x).
  done.
  simpl.
  move => m mu'.
  move/eqP; rewrite if_eq_Some; move/andP; elim.
  move => Hm /eqP <-.
  rewrite measE => ->; rewrite !measE.
  apply id_closure.
  destruct x as [[s |] [s' |]]; rewrite //=.
  simpl in Hm.
  apply/andP; split; rewrite !measE //=.
  move/eqP: Hm => Hm; injection Hm => <-.
  simpl.
  
  admit.

  rewrite -(eqP Hm).
   
  destruc
  destruct x as [s a].
  simpl.
  apply closure_bind => y Hy.
  rewrite !measE; simpl.
  apply id_closure.
  apply/andP; split.
  simpl in y.
  destruct y as [[ [s |] [s' |]] ]; simpl.
  elim o; simpl.
  elim; simpl.
  elim.
  simpl.
  destruct 
  elim y 
  elim y.
  simpl.
  rewrite !measE.

  apply id_closure; apply/andP; split; simpl; rewrite !measE.
  Check app_v.
  apply/eqP; 

  apply/or3P; apply Or31; rewrite eq_refl //=.

  move => c mu eta t Hc.
  rewrite mem_seq1 in Hc; rewrite (eqP Hc) {Hc}.
  rewrite //= !measE //=.
  
  move/or3P; elim.

  (* start case *)
  move/andP; elim; move/eqP => -> /eqP <-; simpl.

  rewrite !measE; simpl.
  apply id_closure.
  apply (app_v_equienabledP OI1 OI2).
  done.
  done.
  done.
  done.
  rewrite !measE //=.
  move => _; apply/andP; split.
  apply/or3P; apply Or31; rewrite !measE //= !eq_refl //=.
  done.


  (* second case *)
  move/andP; elim.
  move/eqP => -> /eqP <-; rewrite !measE.
  apply id_closure; apply/andP; split.
  apply/or3P; apply Or32.

  rewrite /OIR1; apply/andP; split. 
  rewrite !measE.
  apply/eqP.
  apply mbind_eqP => x Hx.
  rewrite !measE //=.
  case: (app_vP OI1 true (Some x, None)); rewrite //=.
  move => _ ->; rewrite !measE //=.
  apply/eqP; munder (rewrite !measE).
  done.
  apply/eqP; munder (rewrite !measE).
  done.

  (* last case *)
  move/existsP; elim => x; move/existsP; elim => i; move/andP; elim; move/eqP => -> /eqP ->.
  rewrite !measE.
  simpl.
  apply id_closure.
  apply (app_v_equienabledP OI1 OI2); rewrite //=.
  rewrite /v_chan_equienabled /v_chan_enabled /enabled //=.
  exunder (rewrite if_neq_None).
  have -> :
    [exists a, Some (i + x)%R == Some a] by apply/existsP; eexists; apply eq_refl.
  have -> :
    [exists a, Some i == Some a] by apply/existsP; eexists; apply eq_refl.
  done.

  move => m m' d d'.
  move/eqP; rewrite if_eq_Some; move/andP; elim => h1 h2.
  move/eqP; rewrite if_eq_Some; move/andP; elim => h3 h4.
  rewrite !measE; munder (rewrite measE).
  apply/andP; split.
  apply/or3P; apply Or33.
  rewrite -(eqP h2) -(eqP h4); rewrite !measE.
  apply/existsP; eexists; apply/existsP; eexists.
  apply/andP; split.
  simpl.
  apply eq_refl.
  done.
  rewrite -(eqP h2) -(eqP h4) !measE //=.
  admit.
  rewrite !measE //=.
  move => _; apply/andP; split.
  apply/or3P; apply Or33.
  apply/existsP; eexists; apply/existsP; eexists.
  apply/andP; split.
  rewrite !measE; apply eq_refl.
  rewrite !measE //=.
  rewrite !measE //=.

  simpl.
  move => h mu eta t.
  move/or3P; elim.
  move/andP; elim; move/eqP => -> /eqP ->; rewrite !measE.
  apply id_closure.
  apply/andP; split.
  apply/or3P; apply Or32.
  munder (rewrite measE).
  
  
  rewrite 
  case: (app_hP OI1).
  apply (app_h_equienabledP OI1 OI2).
  

  done.
  rewrite /enabled //= .

  move/(_ (i + x)%R).
  rewrite eq_refl //=.

  move => _
  
  
  rewrite eq_refl.

  move/andP.

  move => m
  don
  
  (* TODO here *)
  apply m
  rewrite /OIR2.

  simpl.
  apply (app_v_equienabledP OI1 OI2); rewrite //=.
  rewrite !measE.
  move=> _.
  apply id_closure.
  apply/andP; split.
  apply/orP; left; apply/orP; right.
  rewrite /OIR1 !measE.
  rewrite eq_refl.
  
  rewrite /v_chan_equienabled /v_chan_enabled.
  rewrite /enabled //=.
  
  done.

  simpl.

  rewrite mem_seq1 in Hc; rewrite (eqP Hc) //=.
  rewrite !measE //=.

  move => _; apply/andP; split; rewrite !measE //=.
  apply/orP; left; apply/orP; left; rewrite !eq_refl //=.
  simpl; rewrite !measE.
  rewrite mem_seq1 in Hc; rewrite (eqP Hc).
  move/andP; elim; move/eqP => -> /eqP <-; rewrite !measE.
  apply/andP; split.
  apply/orP; right; apply/existsP.
  eexists; apply/existsP; eexists.
  apply/andP; split.
  rewrite !measE.
  apply/eqP.
  munder (rewrite !measE).
  mun
  munder (rewrite !measE); rewrite measE.
  
  elim (app_vP OI1 true (Some x, None)).
  case: app_vP.
  apply/eqP.

  rewrite mbindA.
  rewrite measE.
  apply mbind_
  rewrite !measE.
  exists 
  munder (rewrite measE).

  mov
  apply/andP; split.
  rewrite /

  apply/orP; left; apply/orP; left.
  rewrite /
  move => m m' d d'; move/eqP; rewrite if_eq_Some; move/andP; elim; move/eqP => -> /eqP <- //= => He; injection He => <-.
  rewrite !measE //=.
  Check app_v_equienabledP.
  
  done.
  done.
  done.
  simpl.
  
  move => m m' mu' eta'.
  move/eqP;
  rewrite if_eq_Some.
  move/andP; elim; move/eqP => -> /eqP <-.
  simpl => Heq; injection Heq => <-.
  rewrite !measE //=.
  rewrite /RTr; apply/andP; split.
  apply/orP; left; apply/orP; left.
  rewrite !measE //= !eq_refl //=.
  rewrite !measE //= .

  rewrit
  
  appl
  simpl.
  move/eqP. rewrite if_eq_Some.
  simpl.

  

  rewrite !mbindA !ret_bind !mbindA.
  munder (rewrite !measE).
  rewrite //= mem_seq1 in Hc; rewrite (eqP Hc).
  rewrite /RTr; apply/andP; split.
  apply/orP; left; apply/orP; left; apply/andP; split.
  apply/eqP; rewrite !mbindA.
  Check mbind_irrel.
  apply (app_v_equienabledP.
  move/
  rewrite /outputs //= in Hc.
                             