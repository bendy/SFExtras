(* (Deeply Embedded) Church Encoded Datatypes in Coq. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

  (* Somewhat counterintuitively, we're going to first add numbers to
     our definition of the lambda calculus, then show how we didn't
     really 'need' them in the first place (but they're certainly nice
     to have)! *)

  (* Since numbers make for realistic programs, let's add them to our
     lambda calculus!*)
  Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> tm -> tm
  | tm_zero  : tm
  | tm_succ  : tm -> tm
  | tm_iter  : tm -> tm -> tm -> tm.

  (* We define three things: zero and successor constructors for
     number, and an interator for recursing over / destructing numbers
     *)

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "'iter' x 'zero=>' y 'succ=>' z" :=
  (tm_iter x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).

Notation "'S' x" := (tm_succ x) (in custom stlc at level 1, left associativity).

Notation "\ x , y" :=
  (tm_abs x y) (in custom stlc at level 90, x at level 99,
                     y custom stlc at level 99,
                     left associativity).

Coercion tm_var : string >-> tm.
Open Scope string_scope.

(** Some more notation magic to set up the concrete syntax, as we did
    in the [Imp] chapter... *)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition w : string := "w".
Definition t : string := "t".
Definition f : string := "f".
Definition s : string := "s".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold w : core.
Hint Unfold s : core.


(** Some examples... *)

Definition two : tm := <{S (S tm_zero) }>.

Print Nat.add.
Definition plus_tm : tm :=
  <{\x, \y, iter x zero=> y succ=> (\w, S w) }>.

Definition mult_tm : tm :=
  <{\x, \y, iter x zero=> tm_zero succ=> (\z, plus_tm y z) }>.

(* ################################################################# *)
(** * Operational Semantics *)

(* ================================================================= *)
(** ** Values *)

(** Numbers are now values: *)
(* Following our previous convention for lambda abstractions, we don't
   require the subterm of a successor to be a value.  *)
Inductive value : tm -> Prop :=
  | v_abs : forall x t1,
      value <{\x, t1}>
  | v_zero : value tm_zero
  | v_succ : forall t1, value <{S t1}>.

Hint Constructors value : core.

(* ================================================================= *)
(** ** LC+Nat Programs *)

(* ================================================================= *)
(** ** Substitution *)

(** Can you fill in the rest of the substitution function?

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x, t)         = \x:T, t
       [x:=s](\y, t)         = \y:T, [x:=s]t         if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)

*)

(** ... and formally: *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).













Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x =? y then s else t
  | <{\y, t1}> =>
      if x =? y then t else <{\y, [x:=s] t1}>
  | <{S t1}> => <{S ([x:=s] t1)}>
  | <{t1 t2}> =>
    <{([x:=s] t1) ([x:=s] t2)}>

  | tm_zero => tm_zero     (* NEW *)
  | <{iter z zero=> cz succ=> cs}> => (* NEW *)
    <{iter ([x:=s] z) zero=> ([x:=s] cz) succ=> ([x := s] cs)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(** For example... *)

(* ================================================================= *)
(** ** Reduction *)

(**
                               value v2
                     ---------------------------                     (ST_AppAbs)
                     (\x,t1) v2 --> [x:=v2]t1

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'

                           t1 --> t1'
               --------------------------
               iter t1 zero=> cz succ=> cs --> iter t1' zero=> cz succ=> cs

               --------------------------
          iter tm_zero zero=> cz succ=> cs --> cz

              ----------------------------
          iter (tm_succ t1) z zero=> cz succ=> cs -->
          cs (iter t1 z zero=> cz succ=> cs)
*)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x t1 v2, (* <- beta reduction *)
         value v2 ->
         <{(\x, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>

  (* NEW RULES: *)
  | ST_Zero : forall cz cs,
      <{iter tm_zero zero=> cz succ=> cs}> --> cz

  | ST_Succ : forall t1 cz cs,
      <{iter (S t1) zero=> cz succ=> cs}> --> <{cs (iter t1 zero=> cz succ=> cs) }>

  | ST_Iter : forall t1 t1' cz cs,
      t1 --> t1' ->
      <{iter t1 zero=> cz succ=> cs}> -->
      <{iter t1' zero=> cz succ=> cs}>

where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


(* We can once again reason about the execution of terms using
   theorems. *)
Example plus_two_ex :
  <{plus_tm two two}> -->* <{S (S (S (S tm_zero))) }>.
Proof.
  eapply multi_step.
  { unfold plus_tm, two.
    apply ST_App1.
    apply ST_AppAbs.
    apply v_succ. }
  simpl; eapply multi_step.
  { simpl.
    apply ST_AppAbs.
    apply v_succ. }
  simpl; eapply multi_step.
  { eapply ST_Succ. }
  simpl; eapply multi_step.
  { apply ST_App2.
    constructor.
    eapply ST_Succ. }
  simpl; eapply multi_step.
  { apply ST_App2.
    constructor.
    apply ST_App2.
    constructor.
    eapply ST_Zero. }
  simpl. eapply multi_step.
  { eapply ST_App2. constructor.
    apply ST_AppAbs.
    apply v_succ. }
  simpl. eapply multi_step.
  { apply ST_AppAbs.
    constructor. }
  simpl. apply multi_refl.
Qed.

(* That was exhausting, and rather mechanical. Can we do better?  Yes,
   proof automation to the rescue!  note that at each step, only one
   evaluation rule applies. To know if a rule applies, we just need to
   look at the shape of the goal, and (some of the time), tell if a
   subterm is a value.  *)
Ltac next_step :=
  first [apply ST_AppAbs; solve [repeat constructor]
        | apply ST_App2; solve [repeat constructor]
        | apply ST_Zero
        | apply ST_Succ
        | apply ST_App1; next_step
        | apply ST_Iter; next_step ].

Ltac normalize_lambda :=
  repeat (eapply multi_step;
          [ simpl; next_step | simpl ]).

Example plus_two_ex' :
  <{plus_tm two two}> -->* <{S (S (S (S tm_zero))) }>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* With this tactic, evaluating terms becomes a lot easier :) *)
Example mult_two_ex :
  <{mult_tm two (S tm_zero)}> -->* <{S (S tm_zero) }>.
Proof.
  normalize_lambda.
  apply multi_refl.
Qed.

(* (λx.x x) (λx.x x)*)
Definition omega :=
  <{(\x, x x) (\x, x x) }>.

(* (λx.x x x) (λx.x x x)*)
Definition omega_grow :=
  <{(\x, x x x) (\x, x x x) }>.

(* Note that [normalize_lambda] stops when a normal form is reached.
   For diverging terms, this never happens: *)
Lemma looping_example2 :
    omega -->* omega.
  normalize_lambda.
  do 5 (eapply multi_step;
          [ next_step | ]). simpl.
  apply multi_refl.
Qed.

Lemma looping_example3 :
  omega_grow -->* <{(\x, x x x) (\x, x x x) (\x, x x x) (\x, x x x) }>.
Proof.
  do 15 (eapply multi_step;
         [ next_step | ]). simpl.
  Undo 3.
  do 2 (eapply multi_step;
        [ next_step | ]). simpl.
  constructor.
Qed.
