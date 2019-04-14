Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import boolp classical_sets.

Require Import monad state_monad trace_monad.

(* Contents:
   sample models:
  - for the monads in monad.v, state_monad.v, trace_monad.v
  - for the nondeterministic-state monad
  - for the probability monad.
      depends on the formalization of distributions from the infotheo library
      (https://github.com/affeldt-aist/infotheo).
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section classical_sets_extra.

Hypothesis prop_ext : ClassicalFacts.prop_extensionality.

(* from master branch *)
(*Lemma setUA A : associative (@setU A).
Proof. move=> p q r; rewrite /setU predeqE => a; tauto. Qed.
Lemma setUid A : idempotent (@setU A).
Proof. move=> p; rewrite /setU predeqE => a; tauto. Qed.
Lemma setUC A : commutative (@setU A).
Proof. move=> p q; rewrite /setU predeqE => a; tauto. Qed.*)

Lemma bigset1U A B a (f : A -> set B) : bigsetU [set a] f = f a.
Proof.
apply functional_extensionality => b; apply prop_ext.
split => [[a' <-] //| ?]; by exists a.
Qed.
Lemma bigsetU1 A (s : set A) : bigsetU s (@set1 A) = s.
Proof.
apply functional_extensionality => b; apply prop_ext.
split.
- by move=> -[a ?]; rewrite /set1 => ->.
- by move=> ?; rewrite /bigsetU; exists b.
Qed.
Lemma bigsetUA A B C (s : set A) (f : A -> set B) (g : B -> set C) :
  bigsetU (bigsetU s f) g = bigsetU s (fun x => bigsetU (f x) g).
Proof.
apply functional_extensionality => c; apply prop_ext.
split => [[b [a' aa' ?] ?]|[a' aa' [b ? ?]]].
by exists a' => //; exists b.
by exists b => //; exists a'.
Qed.

Lemma setUDl : BindLaws.bind_left_distributive (fun I A => @bigsetU A I) (@setU).
Proof.
move=> A B /= p q r; apply functional_extensionality => b; apply prop_ext; split.
move=> -[a [?|?] ?]; by [left; exists a | right; exists a].
rewrite /setU => -[[a ? ?]|[a ? ?]]; exists a; tauto.
Qed.

End classical_sets_extra.

Module ModelMonad.

Section identity.
Local Obligation Tactic := by [].
Program Definition identity := (@Monad_of_bind_ret _ (fun A B (a : id A) (f : A -> id B) => f a) (fun A (a : A) => a)_ _ _).
End identity.

Section list.
Local Obligation Tactic := idtac.
Program Definition list := @Monad_of_bind_ret _ (fun A B (a : seq A) (f : A -> seq B) => flatten (map f a)) (fun A (a : A) => [:: a]) _ _ _.
Next Obligation. move=> ? ? ? ? /=; by rewrite cats0. Qed.
Next Obligation. move=> ? ?; by rewrite flatten_seq1. Qed.
Next Obligation.
move=> A B C; elim=> // h t IH f g /=; by rewrite map_cat flatten_cat IH.
Qed.
End list.

Section option.
Local Obligation Tactic := idtac.
Program Definition option := @Monad_of_bind_ret option_choiceType (fun A B (a : option A) (f : A -> option B) =>
    if a isn't Some x then None else f x) (@Some) _ _ _.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> ?; by case. Qed.
Next Obligation. move=> ? ? ?; by case. Qed.
End option.

Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set := @Monad_of_bind_ret _ (fun I A => @bigsetU A I) (@set1) _ _ _.
Next Obligation. move=> ? ? ? ?; exact: bigset1U. Qed.
Next Obligation. move=> ? ?; exact: bigsetU1. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: bigsetUA. Qed.
End set.

Section state.
Variables (S T : choiceType).
Let m0 := fun A : choiceType => [choiceType of (S * list T) -> (A * (S * list T))].
Definition state : monad.
refine (@Monad_of_bind_ret m0
  (fun A B m f => fun s => let (a, s') := m s in f a s') (* bind *)
  (fun A a => fun s => (a, s)) (* ret *)
   _ _ _).
by [].
move=> A f; apply functional_extensionality => ?; by case: f.
move=> A B C a b c; apply functional_extensionality => ?; by case: a.
Defined.
End state.

End ModelMonad.

Module ModelFail.

Section option.
Local Obligation Tactic := by [].
Program Definition option_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.option (@None) _).
Definition option := MonadFail.Pack option_class.
End option.

Section list.
Local Obligation Tactic := by [].
Program Definition list_class := @MonadFail.Class _ _
  (@MonadFail.Mixin ModelMonad.list (@nil) _).
Definition list := MonadFail.Pack list_class.
End list.

Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadFail.Class _ _
  (@MonadFail.Mixin (ModelMonad.set prop_ext) (@set0) _).
Next Obligation.
move=> A B f /=; apply functional_extensionality => b; apply prop_ext.
by split=> // -[a []].
Qed.
Definition set := MonadFail.Pack set_class.
End set.

End ModelFail.

Module ModelAlt.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin ModelMonad.list (@cat) catA _).
Next Obligation.
move=> A B /= s1 s2 k.
rewrite !bindE /Join /= /Monad_of_bind_ret.join /=.
by rewrite Monad_of_bind_ret.fmapE map_cat flatten_cat map_cat flatten_cat.
Qed.
Definition list := MonadAlt.Pack list_class.
End list.

Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAlt.Class _ _
  (@MonadAlt.Mixin (ModelMonad.set prop_ext) (@setU) _ _).
Next Obligation. exact: setUA. Qed.
Next Obligation.
rewrite /BindLaws.bind_left_distributive /= => A B m1 m2 k.
rewrite !bindE /Join /= /Monad_of_bind_ret.join /= Monad_of_bind_ret.fmapE /=.
by rewrite setUDl // setUDl.
Qed.
Definition set := MonadAlt.Pack set_class.
End set.

End ModelAlt.

Module ModelAltCI.

(* finite sets form the initial model *)
Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadAltCI.Class _
  (ModelAlt.set_class prop_ext) (@MonadAltCI.Mixin _ (@setU) _ _).
Next Obligation. exact: setUid. Qed.
Next Obligation. exact: setUC. Qed.
Definition set := MonadAltCI.Pack set_class.
End set.

End ModelAltCI.

Module ModelNondet.

Section list.
Local Obligation Tactic := idtac.
Program Definition list_class := @MonadNondet.Class _
  ModelFail.list_class (MonadAlt.mixin ModelAlt.list_class) _.
Next Obligation. apply: MonadNondet.Mixin => //= A l; by rewrite cats0. Qed.
Definition list := MonadNondet.Pack list_class.
End list.

Section set.
Hypothesis prop_ext : ClassicalFacts.prop_extensionality.
Local Obligation Tactic := idtac.
Program Definition set_class := @MonadNondet.Class _
  (ModelFail.set_class _) (MonadAlt.mixin (ModelAlt.set_class prop_ext)) _.
Next Obligation.
apply: MonadNondet.Mixin => //= A p; apply functional_extensionality => a;
  apply prop_ext; rewrite /Fail /= /set0 /setU; split; tauto.
Qed.
Definition set := MonadNondet.Pack list_class.
End set.

End ModelNondet.

Module ModelStateTrace.

Section st.
Variables (S T : choiceType).
Local Obligation Tactic := idtac.
Program Definition mk : stateTraceMonad S T :=
let m := Monad.class (@ModelMonad.state S T) in
let stm := @MonadStateTrace.Class S T _ m
(@MonadStateTrace.Mixin _ _ (Monad.Pack m)
 (fun s => (s.1, s)) (* st_get *)
 (fun s' s => (tt, (s', s.2))) (* st_put *)
 (fun t s => (tt, (s.1, rcons s.2 t))) (* st_mark *)
 _ _ _ _ _ _) in
@MonadStateTrace.Pack S T _ stm.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=> *; by apply functional_extensionality; case. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
End st.
End ModelStateTrace.

Module ModelRun.

Definition mk {S T : choiceType} : runMonad (S * seq T).
set m := @ModelMonad.state S T.
refine (@MonadRun.Pack _ _ (@MonadRun.Class _ _ (Monad.class m)
  (@MonadRun.Mixin _ m
  (fun A m (s : S * list T) => m s) (* run *) _ _))).
by [].
move=> A B m0 f s.
rewrite !bindE /=.
rewrite Monad_of_bind_ret.fmapE /= /Join /= /Monad_of_bind_ret.join /=.
by destruct (m0 s).
Defined.

End ModelRun.

Module ModelStateTraceRun.

Definition mk {S T : choiceType} :
  stateTraceRunMonad S T.
refine (let stm := @ModelStateTrace.mk S T in
        let run := @ModelRun.mk S T in
@MonadStateTraceRun.Pack S T (fun A : choiceType => [choiceType of (S * list T) -> (A * (S * list T))])
  (@MonadStateTraceRun.Class S T (fun A : choiceType => [choiceType of (S * list T) -> (A * (S * list T))])
    (MonadStateTrace.class stm)
    (MonadRun.mixin (MonadRun.class run))
    (@MonadStateTraceRun.Mixin _ _ run _ _ _ _ _ _))).
by [].
by [].
by [].
Defined.

End ModelStateTraceRun.

From mathcomp Require Import bigop finmap.

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
Variables (T : choiceType) (I : eqType) (r : seq I).
(* In order to avoid "&& true" popping up everywhere,
 we prepare a specialized version of bigfcupP *)
Lemma bigfcupP' x (F : I -> {fset T}) :
  reflect (exists2 i : I, (i \in r) & x \in F i)
          (x \in \bigcup_(i <- r | true) F i).
Proof.
apply: (iffP idP) => [|[i ri]]; last first.
  by apply: fsubsetP x; rewrite bigfcup_sup.
rewrite big_seq_cond; elim/big_rec: _ => [|i _ /andP[ri Pi] _ /fsetUP[|//]].
  by rewrite in_fset0.
by exists i; rewrite ?ri.
Qed.
End BigOps.
End PR.

Module ModelBacktrackableState.
Local Open Scope fset_scope.

Section monad.
Variable S : choiceType.
Local Obligation Tactic := try by [].

Program Definition _monad : monad := @Monad_of_bind_ret
(fun A : choiceType => [choiceType of S -> {fset (A * S)}])
(fun A B m (f : A -> S -> {fset (B * S)}) =>
     fun s => \bigcup_(i <- (fun x => f x.1 x.2) @` (m s)) i) (* bind *)
(fun A (a : A) s => [fset (a, s)]) (* ret *) _ _ _.
Next Obligation.
move=> A B /= m f; extensionality s; by rewrite imfset_set1 /= big_seq_fset1.
Qed.
Next Obligation.
move=> A B /=; extensionality s.
apply/fsetP => /= x; apply/bigfcupP'; case: ifPn => xBs.
  exists [fset x]; last by rewrite inE.
    apply/imfsetP; exists x => //=.
  by rewrite {xBs}; case: x.
case => /= SA /imfsetP[] /= sa saBs ->{SA}; rewrite inE => /eqP Hx.
move: xBs; rewrite Hx; apply/negP; rewrite negbK; by case: sa saBs Hx.
Qed.
Next Obligation.
move=> A B C /= m f g; extensionality s.
apply/fsetP => /= x; apply/bigfcupP'/bigfcupP'; case => /= CS  /imfsetP[/=].
- move=> bs /bigfcupP'[/= BS]  /imfsetP[/= sa] sams ->{BS} bsfsa ->{CS} xgbs.
  exists (\bigcup_(i <- [fset g x0.1 x0.2 | x0 in f sa.1 sa.2]) i).
    by apply/imfsetP => /=; exists sa.
  apply/bigfcupP'; exists (g bs.1 bs.2) => //; by apply/imfsetP => /=; exists bs.
- move=> sa sams ->{CS} /bigfcupP'[/= CS]  /imfsetP[/= bs] bsfsa ->{CS} xgbs.
  exists (g bs.1 bs.2) => //; apply/imfsetP => /=; exists bs => //.
  apply/bigfcupP' => /=; exists (f sa.1 sa.2) => //; by apply/imfsetP => /=; exists sa.
Qed.

Lemma BindE (A B : choiceType) m (f : A -> _monad B) :
  (m >>= f) = (fun s => \bigcup_(i <- (fun x => f x.1 x.2) @` (m s)) i).
Proof.
apply functional_extensionality => s.
rewrite /Bind /Join /= /Monad_of_bind_ret.join /=.
set lhs := [fset _ _ | _ in _]. set rhs := [fset _ _ | _ in _].
rewrite (_ : lhs = rhs) //; apply/fsetP => x; rewrite {}/lhs {}/rhs.
apply/idP/imfsetP => /=.
- case/imfsetP => -[a1 a2] /=.
  rewrite /Fun /= /Monad_of_bind_ret.fmap /=.
  case/bigfcupP' => /= b.
  case/imfsetP => -[b1 b2] /= Hb ->{b}.
  by rewrite in_fset1 => /eqP[-> ->{a1 a2} ->{x}]; exists (b1, b2).
- case=> -[a1 s1] Ha /= ->{x}.
  apply/imfsetP => /=.
  rewrite /Fun /= /Monad_of_bind_ret.fmap /=.
  eexists.
  + apply/bigfcupP' => /=.
    eexists.
      apply/imfsetP => /=.
      by exists (a1, s1).
    rewrite in_fset1; apply/eqP; reflexivity.
  + by [].
Qed.

End monad.

Section state.
Variable S : choiceType.
Local Obligation Tactic := try by [].

Program Definition _state : stateMonad S :=
(@MonadState.Pack _ _
  (@MonadState.Class _ _ (Monad.class (_monad S)) (@MonadState.Mixin _ _
(fun s => [fset (s, s)]) (* get *)
(fun s _ => [fset (tt, s)]) (* put *)
_ _ _ _))).
Next Obligation.
move=> s s'; extensionality s''.
rewrite BindE; apply/fsetP => /= x; rewrite inE; apply/bigfcupP'/eqP.
- by case => /= x0 /imfsetP[/= x1]; rewrite inE => /eqP _ ->; rewrite inE => /eqP.
- move=> -> /=; exists [fset (tt, s')]; last by rewrite inE.
  by apply/imfsetP => /=; exists (tt, s) => //; rewrite inE.
Qed.
Next Obligation.
move=> s; extensionality s'.
rewrite 2!BindE /=; apply/fsetP => /= x; apply/bigfcupP'/bigfcupP'.
- case => /= x0 /imfsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE /= => /eqP ->.
  exists [fset (s, s)]; last by rewrite inE.
    apply/imfsetP => /=; exists (tt, s) => //; by rewrite inE.
- case => /= x0 /imfsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE => /eqP ->.
  exists [fset (s ,s)]; last by rewrite inE.
  by apply/imfsetP => /=; exists (tt, s) => //; rewrite inE.
Qed.
Next Obligation.
extensionality s.
rewrite BindE /skip /= /Ret; apply/fsetP => /= x; apply/bigfcupP'/idP.
- by case => /= x0 /imfsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE.
- rewrite inE => /eqP ->; exists [fset (tt, s)]; last by rewrite inE.
  apply/imfsetP; exists (s, s) => //; by rewrite inE.
Qed.
Next Obligation.
move=> A k; extensionality s.
rewrite 2!BindE; apply/fsetP => x; apply/bigfcupP'/bigfcupP'.
- case => /= x0 /imfsetP[/= x1]; rewrite inE => /eqP -> ->.
  rewrite BindE => /bigfcupP'[/= x2]  /imfsetP[/= x3].
  rewrite inE => /eqP -> /= -> xkss.
  exists (k s s s) => //; apply/imfsetP; exists (s, s) => //; by rewrite inE.
- case => /= x0 /imfsetP[/= x1]; rewrite inE => /eqP -> -> /= xksss.
  exists (\bigcup_(i <- [fset k (s, s).1 x2.1 x2.2 | x2 in [fset ((s, s).2, (s, s).2)]]) i).
    apply/imfsetP ; exists (s, s); by [rewrite inE | rewrite BindE].
  apply/bigfcupP'; exists (k s s s) => //;   apply/imfsetP; exists (s, s) => //=; by rewrite inE.
Qed.

End state.

Section fail.
Variable S : choiceType.
Program Definition _fail : failMonad := @MonadFail.Pack _
  (@MonadFail.Class _ (Monad.class (_monad S))
    (@MonadFail.Mixin _ (fun (A : choiceType) (_ : S) => fset0) _)).
Next Obligation.
move=> A B g; extensionality s; apply/fsetP => x; rewrite inE BindE; apply/negbTE.
apply/bigfcupP'; case => /= x0 /imfsetP[/= sa]; by rewrite inE.
Qed.

End fail.

Section alt.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition _alt : altMonad := @MonadAlt.Pack _
  (@MonadAlt.Class _ (@Monad.class (_monad S))
    (@MonadAlt.Mixin (_monad S)
      (fun (A : choiceType) (a b : S -> {fset A * S}) (s : S) => a s `|` b s) _ _)).
Next Obligation. by move=> A a b c; extensionality s; rewrite fsetUA. Qed.
Next Obligation.
move=> A B /= m1 m2 k; extensionality s; rewrite !BindE /=.
apply/fsetP => /= bs; rewrite !inE; apply/bigfcupP'/orP.
- case => /= BS /imfsetP[/= sa]; rewrite inE => /orP[sam1s ->{BS} Hbs|sam2s ->{BS} Hbs].
  + left; apply/bigfcupP' => /=; exists (k sa.1 sa.2) => //; apply/imfsetP; by exists sa.
  + right; apply/bigfcupP' => /=; exists (k sa.1 sa.2) => //; apply/imfsetP; by exists sa.
- case => /bigfcupP'[/= BS /imfsetP[/= sa sams ->{BS} bsksa]].
  by exists (k sa.1 sa.2) => //; apply/imfsetP; exists sa => //; rewrite inE sams.
  by exists (k sa.1 sa.2) => //; apply/imfsetP; exists sa => //; rewrite inE sams orbT.
Qed.

End alt.

Section nondet.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition nondetbase : nondetMonad :=
  @MonadNondet.Pack _ (@MonadNondet.Class _ (@MonadFail.class (_fail S))
    (@MonadAlt.mixin (_alt S) _) (@MonadNondet.Mixin _ _ _ _)).
Next Obligation. move=> A /= m; extensionality s; by rewrite fset0U. Qed.
Next Obligation. move=> A /= m; extensionality s; by rewrite fsetU0. Qed.
End nondet.

Section nondetstate.

Variable S : choiceType.
Local Obligation Tactic := try by [].
Program Definition nondetstate : nondetStateMonad S :=
  @MonadNondetState.Pack _ _
    (@MonadNondetState.Class _ _ (MonadNondet.class (nondetbase S))
      (MonadState.mixin (MonadState.class (_state S))) (@MonadNondetState.Mixin _ _ _)).
Next Obligation.
move=> A B /= g; rewrite !BindE /=; extensionality s; apply/fsetP => /= sa.
apply/idP/idP/bigfcupP'.
case => /= SA /imfsetP[/= bs bsgs ->{SA}]; by rewrite inE.
Qed.
Next Obligation.
move=> A B /= m k1 k2; extensionality s; rewrite !BindE /=; apply/fsetP => /= bs.
apply/bigfcupP'/idP.
- case => /= BS /imfsetP[/= sa sams ->{BS}]; rewrite inE => /orP[bsk1|bsk2].
  + rewrite inE; apply/orP; left; apply/bigfcupP'; exists (k1 sa.1 sa.2) => //.
    apply/imfsetP; by exists sa.
  + rewrite inE; apply/orP; right; apply/bigfcupP'; exists (k2 sa.1 sa.2) => //.
    apply/imfsetP; by exists sa.
- rewrite inE => /orP[|] /bigfcupP'[/= BS] /imfsetP[/= sa sams ->{BS}] bsk.
  exists (k1 sa.1 sa.2 `|` k2 sa.1 sa.2).
    apply/imfsetP; by exists sa.
  by rewrite inE bsk.
  exists (k1 sa.1 sa.2 `|` k2 sa.1 sa.2).
    apply/imfsetP; by exists sa.
  by rewrite inE bsk orbT.
Qed.

End nondetstate.

End ModelBacktrackableState.

From infotheo Require Import Reals_ext ssr_ext dist convex.
Require Import proba_monad.

Module MonadProbModel.
Local Obligation Tactic := idtac.

Program Definition monad : Monad.t :=
  @Monad_of_bind_ret _ DistBind.d Dist1.d _ _ _.
Next Obligation. move=> ? ? ? ?; exact: DistBind1f. Qed.
Next Obligation. move=> ? ?; exact: DistBindp1. Qed.
Next Obligation. move=> ? ? ? ? ?; exact: DistBindA. Qed.

Lemma BindE (A B : choiceType) m (f : A -> monad B) :
  (m >>= f) = DistBind.d m f.
Proof.
rewrite /Bind /Join /= /Monad_of_bind_ret.join /Fun /=.
rewrite /Monad_of_bind_ret.fmap DistBindA; congr DistBind.d.
by apply functional_extensionality => a; rewrite /= DistBind1f.
Qed.

Program Definition prob_mixin : MonadProb.mixin_of monad :=
  @MonadProb.Mixin monad (fun p (A : choiceType) (m1 m2 : Dist A) =>
    (@Conv2Dist.d A m1 m2 p)) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv0. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv1. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convC. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convmm. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? ?] /=; exact: Conv2Dist.convA. Qed.
Next Obligation.
by move=> ? ? ? ? ? ?; rewrite !BindE Conv2Dist.bind_left_distr.
Qed.

Definition prob_class : MonadProb.class_of Dist :=
  @MonadProb.Class _ _ prob_mixin.

Definition prob : MonadProb.t := MonadProb.Pack prob_class.

End MonadProbModel.
