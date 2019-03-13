From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import choice path finset finfun fintype bigop.
From mathcomp
Require Import bigenough.
From mathcomp Require Import finmap.
Require Import Reals.
From infotheo Require Import ssrR proba dist.

Local Open Scope fset_scope.

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

(*
Definition fset_map_dep {A B : choiceType}
  (s : {fset A}) (f : forall (x : A), x \in s -> B) : {fset B}.
Admitted.
*)

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

Definition join_map {A B : choiceType}
  (f : A -> {fset B}) (s : {fset A}) : {fset B} :=
fset_join (fset_map f s).

Definition fset_cartesian {A : choiceType} (s : {fset {fset A}}) :
  {fset {fset A}} :=
foldr
  (fun xs xss =>
    join_map (fun x => fset_map (fun l => x |` l) xss) xs)
  [fset fset0] s.

Definition dist_fset {A : choiceType} (d : {Dist A}) : {fset (A*R)} :=
fset_map (fun x => (x, d x)) (finsupp d).

Program Definition fset_dist {A : choiceType} (s : {fset (A*R)}) 
  (*H : all (fun ap => 0 <b= ap.2)%R s && \rsum_(ap <- s) ap.2 == 1*) :
  {Dist A} :=
Dist.mk
  (f := @fsfun_of_ffun tt A R_eqType (fset_map fst s)
    (fun xH : _ => let (x, _) := xH in
     nth 0%R (fset_map snd s) (find (fun xp => xp.1 == x) s)) (fun _ => 0%R)) _.

Next Obligation.
Admitted.

Definition swap_fset {A : choiceType}
  (d : {fset ({fset A}*R)}) : {fset {fset (A*R)}} :=
fset_cartesian (fset_map (fun sp => fset_map (fun x => (x, sp.2)) sp.1) d).

Check
swap_fset
  ((0 |` (1 |` (2 |` fset0)), (1/3 : R_choiceType)%R) |`
  ((1 |` (3 |` fset0),        (2/3 : R_choiceType)%R) |`
  fset0)).
Check
   ((1, (1/3)%R) |` ((2, (2/3)%R) |` fset0)) |`
  (((1, (1/3)%R) |` ((4, (2/3)%R) |` fset0)) |`
  (((2, (1/3)%R) |` ((2, (2/3)%R) |` fset0)) |`
  (((2, (1/3)%R) |` ((4, (2/3)%R) |` fset0)) |`
  (((3, (1/3)%R) |` ((2, (2/3)%R) |` fset0)) |`
  (((3, (1/3)%R) |` ((4, (2/3)%R) |` fset0)) |`
  fset0))))).

Program Definition swap {A : choiceType}
  (d : {Dist {fset A}}) : {fset {Dist A}} :=
fset_map fset_dist (swap_fset (dist_fset d)).

Definition ret {A : choiceType} (a : A) : {fset {Dist A}} :=
  [fset (Dist1.d a)].

Definition bind {A B : choiceType}
  (s : {fset {Dist A}}) (f : A -> {fset {Dist B}}) : {fset {Dist B}} :=
fset_map dist_join (fset_join (fset_map swap (fset_map (dist_map f) s))).
