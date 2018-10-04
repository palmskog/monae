Require Import FunctionalExtensionality Nat List.
Import ListNotations.
Require Import state_product_monad.

Obligation Tactic := idtac.

(* A model for the stateful monad *)

Program Definition stateful (S : Type) : statefulMonad S := {|
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

(* A model for the state monad *)

Program Definition state (S : Type) : stateMonad S := {|
MonadState.class := {|
  MonadState.base := MonadStateful.class (stateful S) ;
  MonadState.mixin := {|
    MonadState.get := fun s => (s, s) ;
    MonadState.put := fun s' _ => (tt, s')
    |}
  |}
|}.

Solve Obligations with reflexivity.

(* A model for the trace monad *)

Program Definition trace (T : Type) : traceMonad T := {|
MonadTrace.class := {|
  MonadTrace.base := MonadStateful.class (stateful (list T)) ;
  MonadTrace.mixin := {|
    MonadTrace.mark := fun t l => (tt, l ++ [t])
    |}
  |}
|}.

Next Obligation.
reflexivity.
Qed.

(* A model for the state/trace monad *)

Program Definition stateTrace (S T : Type) :
  stateTraceMonad S T := MonadStateTrace.Pack (MonadStateTrace.Class (
  MonadStateTrace.Mixin
    _ _ (Sm := state S) (Tm := trace T)
    (st_monad := stateful _))).

Solve Obligations with reflexivity.

Example tnonce : stateTrace (nat * list nat) nat nat :=
  do n <- Get (stateTrace nat nat);
  do _ <- Put (stateTrace nat nat) (S n);
  do _ <- Mark (stateTrace nat nat) n;
  Ret n.

Compute Run (do n1 <- tnonce ; do n2 <- tnonce; Ret (n1 =? n2)) (0, []).
