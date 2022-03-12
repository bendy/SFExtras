(* S4  *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Import Maps.
From PLF Require Import Smallstep.


(** Types **)
Inductive ty : Type :=
| Ty_Bool  : ty
| Ty_Arrow : ty -> ty -> ty
| Ty_Box : ty -> ty
| Ty_Diamond : ty -> ty.

(** Terms **)

Inductive tm : Type :=
(* Pure STLC terms*)
| tm_var    : string -> tm
| tm_app    : tm -> tm -> tm
| tm_abs    : string -> ty -> tm -> tm
(* Booleans *)
| tm_true   : tm
| tm_false  : tm
| tm_if     : tm -> tm -> tm -> tm
(* Box operators *)
| tm_box    : tm -> tm
| tm_unbox  : string -> tm -> tm -> tm
(* Diamond operators *)
| tm_dia    : tm -> tm
| tm_undia  : string -> tm -> tm -> tm.

Declare Custom Entry stlc_tm.
Declare Custom Entry stlc_ty.
(* Notations for pure STLC types + terms *)
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 50, right associativity).
Notation "( x )" := x (in custom stlc_ty, x at level 99).
Notation "x" := x (in custom stlc_ty at level 0, x constr at level 0).

Notation "<{ e }>" := e (e custom stlc_tm at level 99).
Notation "( x )" := x (in custom stlc_tm, x at level 99).
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0).
Notation "x y" := (tm_app x y) (in custom stlc_tm at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 90, x at level 99,
                     t custom stlc_ty at level 99,
                     y custom stlc_tm at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

(* Notations for boolean expressions + types *)
Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 89,
                    x custom stlc_tm at level 99,
                    y custom stlc_tm at level 99,
                    z custom stlc_tm at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_tm at level 0).

(* Notations for modal operators + types *)
Notation "'□' T" := (Ty_Box T) (in custom stlc_ty at level 50,
                                   T custom stlc_ty at level 51).
Notation "'box' t" := (tm_box t) (in custom stlc_tm at level 0).
Notation "'unbox' x ':=' t1 'in' t2" :=
  (tm_unbox x t1 t2) (in custom stlc_tm at level 90, x at level 99,
                         t1 custom stlc_tm at level 99,
                         t2 custom stlc_tm at level 99,
                         left associativity).
Notation "'♢' T" := (Ty_Diamond T) (in custom stlc_ty at level 50).
Notation "'dia' t" := (tm_dia t) (in custom stlc_tm at level 0).
Notation "'undia' x ':=' t1 'in' t2" :=
  (tm_undia x t1 t2) (in custom stlc_tm at level 90, x at level 99,
                         t1 custom stlc_tm at level 99,
                         t2 custom stlc_tm at level 99,
                         left associativity).

Open Scope string_scope.

(** Some more notation magic to set up the concrete syntax, as we did
    in the [Imp] chapter... *)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition u : string := "u".
Definition w : string := "w".
Definition t : string := "t".
Definition f : string := "f".
Definition g : string := "g".
Definition s : string := "s".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold u : core.
Hint Unfold w : core.
Hint Unfold s : core.

(** Some examples proof terms from Chapter 4: *)

(* quote = λx: □□A. let box u = x in box box u : □□A ⊃ □A *)
Definition quote : tm := <{\x : □□ Bool, unbox u := x in box (box u) }>.

(* apply = λx:□(A ⊃ B). λy:□A. let box u = x in let box w = y in box u w
   : □(Bool ⊃ Bool) ⊃ □Bool ⊃ □A *)
Definition apply : tm := <{\x : □ (Bool -> Bool), \y : □ Bool,
          unbox u := x in
        unbox w := y in box (u w) }>.

(* A proof of □(Bool -> Bool) ⊃ ♢Bool -> ♢Bool *)
(* λx: ♢♢ Bool. dia (let dia y = x in let dia z = y in z)*)
Definition ex_1 : tm := <{\x : ♢♢ Bool, dia (undia y := x in undia z := y in z)}>.

(* A proof of □(Bool -> Bool) ⊃ ♢Bool -> ♢Bool *)
(* λf : □(Bool ⊃ Bool). λx:♢Bool. .let box g = f in dia (let dia y = x in g y)*)
Definition ex_2 : tm := <{\f : □ (Bool -> Bool), \x : ♢ Bool,
          unbox g := f in dia (undia y := x in g y)}>.

(* ################################################################# *)
(** * Operational Semantics *)

(* ================================================================= *)
(** ** Values *)

Inductive value : tm -> Prop :=
| v_abs : forall x T t1,
    value <{\x:T , t1}>
| v_true : value tm_true
| v_false : value tm_false
| v_box : forall t, value <{box t}>
| v_diamond : forall t, value <{dia t}>.

(* ================================================================= *)
(** ** S4 'programs' *)

(* ================================================================= *)
(** ** Substitution *)

(*

[M/x]x = M
[M/x]y = y for x 6 = y
[M/x](λy:A. N ) = λy:A. [M/x]N provided x 6 = y, x 6 ∈ F V (M )
[M/x](N1 N2) = ([M/x]N1) ([M/x]N2)
[M/x](box N ) = box N
[M/x](let box u = N1 in N2) = let box u = [M/x]N1 in [M/x]N2
[M/x](dia E) = dia ([M/x]eE)
[M/x](let dia y = N in F ) = let dia y = [M/x]N in F
[M/x](let box u = N in F ) = let box u = [M/x]N in [M/x]F
[M/x]N = [M/x]N

〈〈let dia y = N in E/x〉〉F = let dia y = N in 〈〈E/x〉〉F
〈〈let box u = N in E/x〉〉F = let box u = N in 〈〈E/x〉〉F
〈〈M/x〉〉F = [M/x]eF

*)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x =? y then s else t
  | <{\y : T , t1}> =>
      if x =? y then t else <{\y : T, [x:=s] t1}>
  | <{t1 t2}> =>
    <{([x:=s] t1) ([x:=s] t2)}>
  (* Booleans *)
  | <{ true }>  =>
      <{ true }>
  | <{ false }> =>
      <{ false }>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>

  (* Box operators *)
  | <{ box t }> =>
      <{ box ([x := s] t) }>
  | <{ unbox y := t1 in t2 }> =>
      if x =? y then <{ unbox y := [x := s] t1 in t2 }>
      else <{ unbox y := [x := s] t1 in [x := s] t2 }>
  (* Diamond operators *)
  | <{ dia t }> =>
      <{ dia ([x := s] t) }>
  | <{ undia y := t1 in t2 }> =>
      <{ undia y := [x := s] t1 in t2 }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).

Reserved Notation "'〈' x ':=' s '〉' t" (in custom stlc_tm at level 20, x constr).

(* This is not the right name... *)
Fixpoint delay (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | <{ undia y := t1 in t2 }> =>
      <{ undia y := t1 in 〈x := s〉 t2 }>
  | t => <{[x := s]t}>
  end

where "'〈' x ':=' s '〉' t" := (delay x s t) (in custom stlc_tm).
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


                    --------------------------------               (ST_IfTrue)
                    (if true then t1 else t2) --> t1

                    ---------------------------------              (ST_IfFalse)
                    (if false then t1 else t2) --> t2

                             t1 --> t1'
      --------------------------------------------------------     (ST_If)
      (if t1 then t2 else t3) --> (if t1' then t2 else t3)

*)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t1 v2, (* <- beta reduction *)
         value v2 ->
         <{(\x : T, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>

(* Booleans *)
| ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
| ST_IfFalse : forall t1 t2,
    <{if false then t1 else t2}> --> t2
| ST_If : forall t1 t1' t2 t3,
    t1 --> t1' ->
    <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

(* Box Operator *)
| ST_Box : forall t1 t1',
    t1 --> t1' ->
    <{ box t1 }> --> <{ box t1' }>
| ST_Unbox : forall x t1 t2,
    <{unbox x := box t1 in t2}> -->
    <{ [x := t1]t2 }>

(* Diamond Operator *)
| ST_Dia : forall t1 t1',
    t1 --> t1' ->
    <{ dia t1 }> --> <{ dia t1' }>
| ST_Undia : forall x t1 t2,
    <{undia x := dia t1 in t2}> -->
    <{ 〈 x := t1〉t2 }>

where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Ltac next_step :=
  first [ apply ST_IfTrue
        | apply ST_IfFalse
        | apply ST_Unbox
        | apply ST_Undia
        | apply ST_AppAbs; solve [repeat constructor]
        | apply ST_App2; solve [repeat constructor]
        | apply ST_App1; next_step
        | apply ST_If; next_step
        | apply ST_Box; next_step
        | apply ST_Dia; next_step ].

Ltac normalize_lambda :=
  repeat (eapply multi_step;
          [ simpl; next_step | simpl ]).
