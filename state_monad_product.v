Require Import Coq.Program.Tactics FunctionalExtensionality.
Require Import List.
Import ListNotations.
Require Import monad.

Obligation Tactic := idtac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The core part of all stateful monads *)
(* REMARK: C'est un cas particulier de monade où le type [m] est forcé mais je
   ne vois pas comment le relier à [monad]. *)

Module MonadStateful.

Section MonadStateful.

Variable S : Type.

Section Class.

Let m (A : Type) : Type := S -> A*S.

Record class_of : Type := Class {
  op_ret : forall A, A -> m A ;
  op_bind : forall A B, m A -> (A -> m B) -> m B ;
  op_run : forall A, m A -> S -> A * S ;
  aaa : Laws.left_neutral op_bind op_ret ;
  bbb : Laws.right_neutral op_bind op_ret ;
  ccc : Laws.associative op_bind ;
  hhh : forall A (a : A) s, op_run (op_ret a) s = (a, s) ;
  iii : forall A B c (f : A -> m B) s,
    op_run (op_bind c f) s = let (a, s') := op_run c s in op_run (f a) s'
}.

End Class.

Record t : Type := Pack { m (A : Type) : Type := S -> A*S ; class : class_of }.

Definition ret (M : t) A : A -> m M A :=
  let: Pack _ (Class x _ _ _ _ _ _ _) := M in x A.

Arguments ret {M A} : simpl never.

Definition bind (M : t) A B : m M A -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ x _ _ _ _ _ _) := M in x A B.

Arguments bind {M A B} : simpl never.

Definition run (M : t) A : m M A -> S -> A * S :=
  let: Pack _ (Class _ _ x _ _ _ _ _) := M in x A.

Arguments run {M A} : simpl never.

End MonadStateful.

Module Exports.

Notation "m >>= f" := (bind m f).
Notation "'do' x <- m ; e" := (m >>= (fun x => e)).
Notation "'do' x : T <- m ; e" := (m >>= (fun x : T => e)) (only parsing).
Notation "m >> f" := (m >>= fun _ => f) (at level 50).
Notation Bind := bind.
Notation Ret := ret.
Notation Run := run.
Notation statefulMonad := t.

Coercion m : statefulMonad >-> Funclass.

End Exports.

End MonadStateful.

Export MonadStateful.Exports.

(* The state monad : a stateful monad with [get] and [put] *)

Module MonadState.

Record mixin_of (S : Type) (M : statefulMonad S) : Type := Mixin {
  get : M S ;
  put : S -> M unit ;
  ddd : forall s s', put s >> put s' = put s' ;
  eee : forall s, put s >> get = put s >> Ret _ s ;
  fff : get >>= put = Ret _ tt ;
  ggg : forall k : S -> S -> M S,
    get >>= (fun s => get >>= k s) = get >>= fun s => k s s ;
  jjj : forall s, Run get s = (s, s) ;
  kkk : forall s s', Run (put s') s = (tt, s')
}.

Record class_of (S : Type) := Class {
  base : MonadStateful.class_of S ;
  mixin : mixin_of (MonadStateful.Pack base) }.

Structure t S : Type := Pack {
  m (A : Type) : Type := S -> A*S ; class : class_of S }.

Definition op_get S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ _)) := M return m M S in x.

Arguments op_get {S M} : simpl never.

Definition op_put S (M : t S) : S -> m M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _ _ _)) := M return S -> m M unit in x.

Arguments op_put {S M} : simpl never.

Definition baseType S (M : t S) := MonadStateful.Pack (base (class M)).

Module Exports.

Notation Get := op_get.
Notation Put := op_put.
Notation stateMonad := t.

Coercion baseType : stateMonad >-> statefulMonad.

Canonical baseType.

End Exports.

End MonadState.

Export MonadState.Exports.

(* The trace monad : a stateful monad with [mark] *)

Module MonadTrace.
Record mixin_of (T : Type) (M : statefulMonad (list T)) : Type := Mixin {
  mark : T -> M unit ;
  lll : forall t l, Run (mark t) l = (tt, l ++ [t])
}.
Record class_of (T : Type) : Type := Class {
  base : MonadStateful.class_of (list T) ;
  mixin : mixin_of (MonadStateful.Pack base) }.
Structure t T := Pack {
  m (A : Type) : Type := list T -> A * list T ; class : class_of T }.
Definition op_mark T (M : t T) : T -> m M unit :=
  let: Pack _ (Class _ (Mixin x _)) := M return T -> m M unit in x.
Arguments op_mark {T M} : simpl never.
Definition baseType T (M : t T) := MonadStateful.Pack (base (class M)).
Module Exports.
Notation Mark := op_mark.
Notation traceMonad := t.
Coercion baseType : traceMonad >-> statefulMonad.
Canonical baseType.
End Exports.
End MonadTrace.
Export MonadTrace.Exports.

(* Algebraic manipulations of functions *)
(* REMARK 1: Ce sont des fonctions qui réarrangent leur entrée mais ne calculent
   rien. [mleft] et [mright] sont utilisées pour faire le produit de deux
   monades stateful (l'une à gauche de l'état produit, et l'autre à droite). *)
(* REMARK 2: Certaines de ces fonctions sont probablement déjà dans la librairie
   de ssreflect. *)

Definition id {A : Type} (a : A) : A := a.

Definition product
  {A1 A2 B1 B2 : Type} (f1 : A1 -> B1) (f2 : A2 -> B2) : A1*A2 -> B1*B2 :=
  fun a => (f1 (fst a), f2 (snd a)).

Definition swap {A B : Type} (x : A * B) : B * A := (snd x, fst x).

Definition assoc {A B C : Type} (x : (A * B) * C) : A * (B * C) :=
  (fst (fst x), (snd (fst x), snd x)).

Definition assoc_inv {A B C : Type} (x : A * (B * C)) : (A * B) * C :=
  ((fst x, fst (snd x)), snd (snd x)).

Definition comp {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).

Notation "g 'o' f" := (comp g f) (at level 40, left associativity).

Definition mleft {A B C D : Type} (f : A -> B * C) : A * D -> B * (C * D):=
  assoc o product f id.

Definition mright {A B C D : Type} (f : A -> B * C) : D * A -> B * (D * C) :=
  assoc o product swap id o assoc_inv o product id f.

(* The state/trace monad with state on the left and trace on the right *)
(* TODO: A reformater sous forme de packed class ?*)

Module MonadStateTrace.

Section MonadStateTrace.

Variables S T : Type.

Variable Sm : stateMonad S.

Variable Tm : traceMonad T.

Program Record stateTraceMonad : Type := {
  st_monad : statefulMonad _ ;
  st_get : st_monad S :=
    mleft (Get (M := Sm));
  st_put : S -> st_monad unit :=
    fun s' => mleft (Put (M := Sm) s') ;
  st_mark : T -> st_monad unit :=
    fun t => mright (Mark (M := Tm) t)
}.

End MonadStateTrace.

End MonadStateTrace.

(* The trace/state monad with trace on the left and state on the right *)
(* TODO: A reformater sous forme de packed class ?*)

Module MonadTraceState.

Section MonadTraceState.

Variables S T : Type.

Variable Sm : stateMonad S.

Variable Tm : traceMonad T.

Program Record traceStateMonad : Type := {
  st_monad : statefulMonad _ ;
  st_get : st_monad S :=
    mright (Get (M := Sm));
  st_put : S -> st_monad unit :=
    fun s' => mright (Put (M := Sm) s') ;
  st_mark : T -> st_monad unit :=
    fun t => mleft (Mark (M := Tm) t)
}.

End MonadTraceState.

End MonadTraceState.

(** * EXAMPLES *)

(* An example of stateful monad *)

Program Example statefulMonadExample (S : Type) : statefulMonad S := {|
  MonadStateful.class := {|
    MonadStateful.op_ret := fun _ a s => (a, s) ;
    MonadStateful.op_bind := fun _ _ m f s => let (a, s') := m s in f a s' ;
    MonadStateful.op_run := fun _ m s => m s
  |}
  |}.

Next Obligation.
compute.
reflexivity.
Qed.

Next Obligation.
compute.
intros S A m.
extensionality s.
destruct (m s); reflexivity.
Qed.

Next Obligation.
compute.
intros S A B C m f g.
extensionality s.
destruct (m s); reflexivity.
Qed.

Next Obligation.
reflexivity.
Qed.

Next Obligation.
reflexivity.
Qed.

(* An example of state monad *)

Program Example stateMonadExample (S : Type) : stateMonad S := {|
MonadState.class := {|
  MonadState.base := MonadStateful.class (statefulMonadExample S) ;
  MonadState.mixin := {|
    MonadState.get := fun s => (s, s) ;
    MonadState.put := fun s' _ => (tt, s')
    |}
  |}
|}.

Next Obligation.
reflexivity.
Qed.

Next Obligation.
reflexivity.
Qed.

Next Obligation.
reflexivity.
Qed.

Next Obligation.
reflexivity.
Qed.

Next Obligation.
reflexivity.
Qed.

Next Obligation.
reflexivity.
Qed.

(* An example of trace monad *)

Example traceMonadExample (T : Type) : traceMonad T := {|
MonadTrace.class := {|
  MonadTrace.base := MonadStateful.class (statefulMonadExample (list T)) ;
  MonadTrace.mixin := {|
    MonadTrace.mark := fun t l => (tt, t::l)
    |}
  |}
|}.

(* The combination of previous examples *)

Example stateTraceMonadExample (S T : Type) :=
  MonadStateTrace.stateTraceMonad
    (stateMonadExample S) (traceMonadExample T).

(* The same combination of previous examples, but the other way round *)

Example traceStateMonadExample (S T : Type) :=
  MonadTraceState.traceStateMonad
    (stateMonadExample S) (traceMonadExample T).
