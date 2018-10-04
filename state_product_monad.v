Require Import ssrfun List.
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

Section Class.

Variable S : Type.

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

Record t S : Type :=
  Pack { m (A : Type) : Type := S -> A*S ; class : class_of S }.

Definition ret S (M : t S) A : A -> m M A :=
  let: Pack _ (Class x _ _ _ _ _ _ _) := M in x A.

Arguments ret {S M A} : simpl never.

Definition bind S (M : t S) A B : m M A -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ x _ _ _ _ _ _) := M in x A B.

Arguments bind {S M A B} : simpl never.

Definition run S (M : t S) A : m M A -> S -> A * S :=
  let: Pack _ (Class _ _ x _ _ _ _ _) := M in x A.

Arguments run {S M A} : simpl never.

End MonadStateful.

Module Exports.

Notation "m >>= f" := (bind m f).
Notation "'do' x <- m ; e" := (m >>= (fun x => e)).
Notation "'do' x : T <- m ; e" := (m >>= (fun x : T => e)) (only parsing).
Notation "m >> f" := (m >>= fun _ => f) (at level 50).
Notation Bind := bind.
Notation Ret := (ret _).
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
  eee : forall s, put s >> get = put s >> Ret s ;
  fff : get >>= put = Ret tt ;
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

Definition mleft {A B C D : Type} (f : A -> B * C) : A * D -> B * (C * D):=
  assoc \o product f id.

Definition mright {A B C D : Type} (f : A -> B * C) : D * A -> B * (D * C) :=
  assoc \o product swap id \o assoc_inv \o product id f.

Module MonadStateTrace.

Section MonadStateTrace.

Program Record mixin_of (S T : Type) (Sm : stateMonad S) (Tm : traceMonad T) :
  Type := Mixin {
  st_monad : statefulMonad _ ;
  st_get : st_monad S :=
    mleft (Get (M := Sm));
  st_put : S -> st_monad unit :=
    fun s' => mleft (Put (M := Sm) s') ;
  st_mark : T -> st_monad unit :=
    fun t => mright (Mark (M := Tm) t) ;
  mark_get : forall t,
    st_mark t >> st_get = do x <- st_get ; st_mark t >> Ret x ;
  mark_put : forall s t,
    st_mark t >> st_put s = st_put s >> st_mark t
}.

Record class_of (S T : Type) := Class {
  base1 : MonadState.class_of S ;
  base2 : MonadTrace.class_of T ;
  mixin : mixin_of (MonadState.Pack base1) (MonadTrace.Pack base2) }.

Structure t S T : Type := Pack {
  m (A : Type) : Type := S * list T -> A * (S * list T) ; class : class_of S T
}.

Definition op_get S T (M : t S T) : m M S :=
  let: Pack (Class _ _ (Mixin _ x _ _ _ _)) := M return m M S in x.

Arguments op_get {S T M} : simpl never.

Definition op_put S T (M : t S T) : S -> m M unit :=
  let: Pack (Class _ _ (Mixin _ _ x _ _ _)) := M return S -> m M unit in x.

Arguments op_put {S T M} : simpl never.

Definition op_mark S T (M : t S T) : T -> m M unit :=
  let: Pack (Class _ _ (Mixin _ _ _ x _ _)) := M return T -> m M unit in x.

Arguments op_mark {S T M} : simpl never.

Definition baseType1 S T (M : t S T) := MonadState.Pack (base1 (class M)).

Definition baseType2 S T (M : t S T) := MonadTrace.Pack (base2 (class M)).

End MonadStateTrace.

Module Exports.

Notation Get := op_get.
Notation Put := op_put.
Notation Mark := op_mark.
Notation stateTraceMonad := t.

Coercion baseType1 : stateTraceMonad >-> stateMonad.
Coercion baseType2 : stateTraceMonad >-> traceMonad.

Canonical baseType1.
Canonical baseType2.

End Exports.

End MonadStateTrace.

Export MonadStateTrace.Exports.
