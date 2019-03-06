From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq choice
  path finset finfun fintype bigop bigenough finmap.
Require Import Reals Lra Nsatz FunctionalExtensionality.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext
  Rbigop proba dist.

Local Open Scope fset.

Obligation Tactic := idtac.

Definition dist_map {A B : choiceType}
  (f : A -> B) (s : {Dist A}) : {Dist B} :=
DistBind.d s (fun x => Dist1.d (f x)).

Definition dist_join {A : choiceType}
  (d : {Dist {Dist A}}) : {Dist A} :=
DistBind.d d (fun d => d).

Definition fset_map {A B : choiceType}
  (f : A -> B) (s : {fset A}) : {fset B} :=
f @` s.

Definition fset_map_dep {A B : choiceType}
  (s : {fset A}) (f : forall (x : A), x \in s -> B) : {fset B}.
Admitted.

Definition fset_join {A : choiceType}
  (s : {fset {fset A}}) : {fset A} :=
\bigcup_(i <- s) i.

Definition fset_ret {A : choiceType} (a : A) : {fset A} :=
[fset a].

Definition fset_bind {A B : choiceType}
  (s : {fset A}) (f : A -> {fset B}) : {fset B} :=
fset_join (fset_map f s).

Definition fset_strength {A B : choiceType}
  (s : {fset A}) (y : B) : {fset (A * B)} :=
fset_map (fun x => (x, y)) s.

Definition fset_cartesian {A : choiceType} (s : {fset {fset A}}) :
  ssrnat.iter #|` s | (fun B : choiceType => prod_choiceType B A) A.
Admitted.

Definition dist_fset {A : choiceType} (d : {Dist A}) : {fset (A*R)} :=
fset_map (fun x => (x, d x)) (finsupp d).

Definition fset_dist_fun {A : choiceType} (s : {fset (A*R)}) :
  {fsfun A -> R for (fun=>0)}.
Admitted.

Program Definition fset_dist {A : choiceType} (s : {fset (A*R)})
  (H : all (fun ap => 0 <b= ap.2)%R s && \rsum_(p <- fset_map snd s) p == 1) :
  {Dist A} :=
Dist.mk (f := fset_dist_fun s) _.

Next Obligation.
intros.
Admitted.

Definition swap_fun {A : choiceType}
  (d : {Dist {fset A}}) : {fset {fsfun A -> R for (fun=>0)}} :=
fset_map fset_dist_fun
  (fset_map (fun sp => fset_strength sp.1 sp.2) (dist_fset d)).

Program Definition swap {A : choiceType}
  (d : {Dist {fset A}}) : {fset {Dist A}} :=
fset_map_dep (swap_fun d) (fun f H => Dist.mk (f := f) _).

Next Obligation.
intros.
Admitted.

Definition ret {A : choiceType} (a : A) : {fset {Dist A}} :=
  [fset (Dist1.d a)].

Definition bind {A B : choiceType}
  (s : {fset {Dist A}}) (f : A -> {fset {Dist B}}) : {fset {Dist B}} :=
fset_map dist_join (fset_join (fset_map swap (fset_map (dist_map f) s))).
