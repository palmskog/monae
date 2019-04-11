Require Import FunctionalExtensionality Reals.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp Require Import finmap (* set *) bigop.
From mathcomp Require Import finset boolp.

From infotheo Require Import Reals_ext ssr_ext dist.
Require Import choicemonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* wip:
  This file provides models:
  - for the nondeterministic-state monad TODO
  - for the probability monad
*)

Section axioms.
Section fun_choiceType.
Definition fun_eqMixin (T1 T2 : eqType) : Equality.mixin_of (T1 -> T2).
Proof.
apply: (@Equality.Mixin _ (fun f g : T1 -> T2 => `[< f =1 g >])) => f g.
apply: (iffP idP) => [/asboolP|->]; [exact/funext|exact/asboolP].
Qed.
Canonical fun_eqType (T1 T2 : eqType) :=
  Eval hnf in EqType (T1 -> T2) (@fun_eqMixin T1 T2).
Axiom fun_choiceMixin : forall (T1 T2 : choiceType), choiceMixin (T1 -> T2).
Canonical fun_choiceType (T1 T2 : choiceType) :=
  Eval hnf in ChoiceType (T1 -> T2) (@fun_choiceMixin T1 T2).
End fun_choiceType.
End axioms.

Section PR.
Local Open Scope fset_scope.
Section ImfsetTh.
Variables (key : unit) (K V : choiceType).
Variable (f : K -> V).
Lemma imfset_set1 x : f @` [fset x] = [fset f x].
Proof.
apply/fsetP => y.
by apply/imfsetP/fset1P=> [[x' /fset1P-> //]| ->]; exists x; rewrite ?fset11.
Qed.
End ImfsetTh.
Section BigOps.
(*
Variables (R : Type) (idx : R).
Variables (op : Monoid.law idx) (aop : Monoid.com_law idx).
Variables I J : finType.
Variable A B : {set I}.
Lemma big_in_fset1 (a : I) (F : I -> R) :
  \big[op/idx]_(i in [fset a]) F i = F a.
Proof. by apply: big_pred1 => i; rewrite inE in_fset1. Qed.
*)
End BigOps.
End PR.

Module ModelBacktrackableState.
Local Open Scope fset_scope.

Section monad.
(*
Variable S : finType.
Local Obligation Tactic := try by [].

Program Definition _monad : choicemonad := @choiceMonad.Pack _
(@choiceMonad.Class (fun A : choiceType => [choiceType of {ffun S -> {fset (A * S)}}])
(fun A (a : A) => [ffun s => [fset (a, s)]]) (* ret *)
(fun A B m (f : A -> {ffun S -> {fset (B * S)}}) =>
     [ffun s => \bigcup_(i <- (fun x => f x.1 x.2) @` (m s)) i]) (* bind *)
_ _ _).
*)
Variable S : choiceType.
Local Obligation Tactic := try by [].

Program Definition _monad : choicemonad := @choiceMonad.Pack _
(@choiceMonad.Class (fun A : choiceType => [choiceType of S -> {fset (A * S)}])
(fun A (a : A) s => [fset (a, s)]) (* ret *)
(fun A B m (f : A -> S -> {fset (B * S)}) =>
     fun s => \bigcup_(i <- (fun x => f x.1 x.2) @` (m s)) i) (* bind *)
_ _ _).
Next Obligation.
move=> A B /= m f; extensionality s; by rewrite imfset_set1 /= big_seq_fset1.
Qed.
Next Obligation.
move=> A B /=; extensionality s.
apply/fsetP => /= x; apply/bigfcupP; case: ifPn => xBs.
  exists [fset x]; last by rewrite in_fset1.
  rewrite andbT; apply/imfsetP; exists x => //=.
  by rewrite {xBs}; case: x.
case => /= SA; rewrite andbT => /imfsetP[] /= sa saBs ->{SA}; rewrite in_fset1 => /eqP Hx.
move: xBs; rewrite Hx; apply/negP; rewrite negbK; by case: sa saBs Hx.
Qed.
Next Obligation.
move=> A B C /= m f g; extensionality s.
apply/fsetP => /= x; apply/bigfcupP/bigfcupP; case => /= CS; rewrite andbT => /imfsetP[/=].
- move=> bs /bigfcupP[/= BS]; rewrite andbT => /imfsetP[/= sa] sams ->{BS} bsfsa ->{CS} xgbs.
  exists (\bigcup_(i <- [fset g x0.1 x0.2 | x0 in f sa.1 sa.2]) i).
    by rewrite andbT; apply/imfsetP => /=; exists sa.
  apply/bigfcupP; exists (g bs.1 bs.2) => //; rewrite andbT; by apply/imfsetP => /=; exists bs.
- move=> sa sams ->{CS} /bigfcupP[/= CS]; rewrite andbT => /imfsetP[/= bs] bsfsa ->{CS} xgbs.
  exists (g bs.1 bs.2) => //; rewrite andbT; apply/imfsetP => /=; exists bs => //.
  apply/bigfcupP => /=; exists (f sa.1 sa.2) => //; rewrite andbT; by apply/imfsetP => /=; exists sa.
Qed.
End monad.

Section state.
Variable S : choiceType.
Local Obligation Tactic := try by [].

Program Definition _state : choicestateMonad S :=
(@choiceMonadState.Pack _ _
  (@choiceMonadState.Class _ _ (choiceMonad.class (_monad S)) (@choiceMonadState.Mixin _ _
(fun s => [fset (s, s)]) (* get *)
(fun s _ => [fset (tt, s)]) (* put *)
_ _ _ _))).
Next Obligation.
move=> s s'; extensionality s''.
rewrite /Bind /=; apply/fsetP => /= x; rewrite in_fset1; apply/bigfcupP/eqP.
- by case => /= x0; rewrite andbT => /imfsetP[/= x1]; rewrite in_fset1 => /eqP _ ->; rewrite in_fset1 => /eqP.
- move=> -> /=; exists [fset (tt, s')]; last by rewrite in_fset1.
  by rewrite andbT; apply/imfsetP => /=; exists (tt, s) => //; rewrite in_fset1.
Qed.
Next Obligation.
move=> s; extensionality s'.
rewrite /Bind /=; apply/fsetP => /= x; apply/bigfcupP/bigfcupP.
- case => /= x0; rewrite andbT => /imfsetP[/= x1]; rewrite in_fset1 => /eqP -> ->; rewrite in_fset1 /= => /eqP ->.
  exists [fset (s, s)]; last by rewrite in_fset1.
  rewrite andbT; apply/imfsetP => /=; exists (tt, s) => //; by rewrite in_fset1.
- case => /= x0; rewrite andbT => /imfsetP[/= x1]; rewrite in_fset1 => /eqP -> ->; rewrite in_fset1 => /eqP ->.
  exists [fset (s ,s)]; last by rewrite in_fset1.
  by rewrite andbT; apply/imfsetP => /=; exists (tt, s) => //; rewrite in_fset1.
Qed.
Next Obligation.
extensionality s.
rewrite /Bind /skip /= /Ret; apply/fsetP => /= x; apply/bigfcupP/idP.
- by case => /= x0; rewrite andbT => /imfsetP[/= x1]; rewrite in_fset1 => /eqP -> ->; rewrite in_fset1.
- rewrite in_fset1 => /eqP ->; exists [fset (tt, s)]; last by rewrite in_fset1.
  rewrite andbT; apply/imfsetP; exists (s, s) => //; by rewrite in_fset1.
Qed.
Next Obligation.
move=> k; extensionality s; rewrite /Bind /=; apply/fsetP => x; apply/bigfcupP/bigfcupP.
- case => /= x0; rewrite andbT => /imfsetP[/= x1]; rewrite in_fset1 => /eqP -> -> /bigfcupP[/= x2]; rewrite andbT => /imfsetP[/= x3].
  rewrite in_fset1 => /eqP -> /= -> xkss.
  exists (k s s s) => //; rewrite andbT; apply/imfsetP; exists (s, s) => //; by rewrite in_fset1.
- case => /= x0; rewrite andbT => /imfsetP[/= x1]; rewrite in_fset1 => /eqP -> -> /= xksss.
  exists (\bigcup_(i <- [fset k (s, s).1 x2.1 x2.2 | x2 in [fset ((s, s).2, (s, s).2)]]) i).
    rewrite andbT; apply/imfsetP; exists (s, s) => //; by rewrite in_fset1.
  apply/bigfcupP; exists (k s s s) => //; rewrite andbT; apply/imfsetP; exists (s, s) => //=; by rewrite in_fset1.
Qed.

End state.

Section fail.
Variable S : choiceType.
Program Definition _fail : choicefailMonad := @choiceMonadFail.Pack _
  (@choiceMonadFail.Class _ (choiceMonad.class (_monad S))
    (@choiceMonadFail.Mixin _ (fun (A : choiceType) (_ : S) => fset0) _)).
Next Obligation.
move=> A B g; extensionality s; apply/fsetP => x; rewrite in_fset0 /Bind; apply/negbTE.
apply/bigfcupP; case => /= x0; rewrite andbT => /imfsetP[/= sa]; by rewrite in_fset0.
Qed.

End fail.

Section alt.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition _alt : choicealtMonad := @choiceMonadAlt.Pack _
  (@choiceMonadAlt.Class _ (@choiceMonad.class (_monad S))
    (@choiceMonadAlt.Mixin (_monad S)
      (fun (A : choiceType) (a b : S -> {fset A * S}) (s : S) => a s `|` b s) _ _)).
Next Obligation. by move=> A a b c; extensionality s; rewrite fsetUA. Qed.
Next Obligation.
move=> A B /= m1 m2 k; extensionality s; rewrite /Bind /=.
apply/fsetP => /= bs; rewrite !in_fset; apply/bigfcupP => /=; case: ifPn.
- rewrite mem_cat => /orP[|] /= BS. ; rewrite andbT => /imfsetP[/= sa]. ; rewrite inE => /orP[sam1s ->{BS} Hbs|sam2s ->{BS} Hbs].
  + left; apply/bigcupP => /=; exists (k sa.1 sa.2) => //; apply/imsetP; by exists sa.
  + right; apply/bigcupP => /=; exists (k sa.1 sa.2) => //; apply/imsetP; by exists sa.
- case => /bigcupP[/= BS /imsetP[/= sa sams ->{BS} bsksa]].
  by exists (k sa.1 sa.2) => //; apply/imsetP; exists sa => //; rewrite inE sams.
  by exists (k sa.1 sa.2) => //; apply/imsetP; exists sa => //; rewrite inE sams orbT.
Qed.

End alt.

Section nondet.

Variable S : finType.
Local Obligation Tactic := try by [].
Program Definition nondetbase : relnondetMonad :=
  @choiceMonadNondet.Pack _ (@choiceMonadNondet.Class _ (@choiceMonadFail.class (_fail S))
    (@choiceMonadAlt.mixin (_alt S) _) (@choiceMonadNondet.Mixin _ _ _ _)).
Next Obligation. move=> A /= m; extensionality s; by rewrite set0U. Qed.
Next Obligation. move=> A /= m; extensionality s; by rewrite setU0. Qed.
End nondet.

Section nondetstate.

Variable S : finType.
Local Obligation Tactic := try by [].
Program Definition nondetstate : relnondetStateMonad S :=
  @choiceMonadNondetState.Pack _ _
    (@choiceMonadNondetState.Class _ _ (choiceMonadNondet.class (nondetbase S))
      (choiceMonadState.mixin (choiceMonadState.class (_state S))) (@choiceMonadNondetState.Mixin _ _ _)).
Next Obligation.
move=> A B /= g; rewrite /Bind /=; extensionality s; apply/setP => /= sa.
apply/bigcupP/idP.
- case => /= SA /imsetP[/= bs bsgs ->{SA}]; by rewrite inE.
- by rewrite inE.
Qed.
Next Obligation.
move=> A B /= m k1 k2; extensionality s; rewrite /Bind /=; apply/setP => /= bs.
apply/bigcupP/idP.
- case => /= BS /imsetP[/= sa sams ->{BS}]; rewrite inE => /orP[bsk1|bsk2].
  + rewrite inE; apply/orP; left; apply/bigcupP; exists (k1 sa.1 sa.2) => //.
    apply/imsetP; by exists sa.
  + rewrite inE; apply/orP; right; apply/bigcupP; exists (k2 sa.1 sa.2) => //.
    apply/imsetP; by exists sa.
- rewrite inE => /orP[|] /bigcupP[/= BS] /imsetP[/= sa sams ->{BS}] bsk.
  exists (k1 sa.1 sa.2 :|: k2 sa.1 sa.2).
    apply/imsetP; by exists sa.
  by rewrite inE bsk.
  exists (k1 sa.1 sa.2 :|: k2 sa.1 sa.2).
    apply/imsetP; by exists sa.
  by rewrite inE bsk orbT.
Qed.

End nondetstate.

End ModelBacktrackableState.
*)

From infotheo Require Import convex.

Module choiceMonadProbModel.
Local Obligation Tactic := idtac.

Program Definition monad : choiceMonad.t := @choiceMonad.Pack Dist
  (@choiceMonad.Class _ Dist1.d DistBind.d _ _ _ ).
Next Obligation. move=> ? ? ? ?; exact: DistBind1f. Qed.
Next Obligation. move=> ? ?; exact: DistBindp1. Qed.
Next Obligation. move=> ? ? ? ? ?; exact: DistBindA. Qed.

Program Definition prob_mixin : choiceMonadProb.mixin_of monad :=
  @choiceMonadProb.Mixin monad (fun p (A : choiceType) (m1 m2 : Dist A) =>
    (@Conv2Dist.d A m1 m2 p)) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv0. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv1. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convC. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convmm. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? ?] /=; exact: Conv2Dist.convA. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: Conv2Dist.bind_left_distr. Qed.

Definition prob_class : choiceMonadProb.class_of Dist :=
  @choiceMonadProb.Class _ _ prob_mixin.

Definition prob : choiceMonadProb.t := choiceMonadProb.Pack prob_class.

End choiceMonadProbModel.
