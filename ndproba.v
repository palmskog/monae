From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq choice
  path finset finfun fintype bigop bigenough finmap.
From infotheo Require Import dist.

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

Definition fset_join {A : choiceType}
  (s : {fset {fset A}}) : {fset A} :=
\bigcup_(i <- s) i.

Program Definition swap {A : choiceType}
  (d : {Dist {fset A}}) : {fset {Dist A}} :=
_.

Next Obligation.
intros A d.
Admitted.

Definition ret {A : choiceType} (a : A) : {fset {Dist A}} :=
  [fset (Dist1.d a)].

Definition bind {A B : choiceType}
  (s : {fset {Dist A}}) (f : A -> {fset {Dist B}}) : {fset {Dist B}} :=
fset_map dist_join (fset_join (fset_map swap (fset_map (dist_map f) s))).
