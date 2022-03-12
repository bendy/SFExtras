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
Notation "'□' T" := (Ty_Box T) (in custom stlc_ty at level 51).
Notation "'box' t" := (tm_box t) (in custom stlc_tm at level 51).
Notation "'unbox' x ':=' t1 'in' t2" :=
  (tm_unbox x t1 t2) (in custom stlc_tm at level 90, x at level 99,
                         t1 custom stlc_tm at level 99,
                         t2 custom stlc_tm at level 99,
                         left associativity).
Notation "'♢' T" := (Ty_Diamond T) (in custom stlc_ty at level 51).
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

(* quote = λx: □□A. let box u = x in box box u : □A ⊃ □□A *)
Definition quote A : tm := <{\x : □ A, unbox u := x in box (box u) }>.

(* apply = λx:□(A ⊃ B). λy:□A. let box u = x in let box w = y in box u w
   : □(Bool ⊃ Bool) ⊃ □Bool ⊃ □A *)
Definition apply A B : tm := <{\x : □ (A -> B), \y : □ A,
          unbox u := x in
        unbox w := y in box (u w) }>.

(* A proof of ♢♢Bool -> ♢Bool *)
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

Reserved Notation "Gamma '|-' t '\in' T"
            (at level 101,
             t custom stlc_tm, T custom stlc_ty at level 0).

Definition context := (partial_map ty * partial_map ty)%type.

Inductive has_type : context -> tm -> ty -> Prop :=
(* Lambda Terms *)
| T_Var1 : forall Delta Gamma x T1,
    Gamma x = Some T1 ->
    (Delta, Gamma) |- x \in T1

| T_Var2 : forall Delta Gamma x T1,
    Delta x = Some T1 ->
    (Delta, Gamma) |- x \in T1
| T_Abs : forall Delta Gamma x T1 T2 t1,
    (Delta, x |-> T2 ; Gamma) |- t1 \in T1 ->
      (Delta, Gamma) |- \x:T2, t1 \in (T2 -> T1)
| T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1

(* Booleans *)
| T_True : forall Gamma,
      Gamma |- true \in Bool
| T_False : forall Gamma,
       Gamma |- false \in Bool
| T_If : forall t1 t2 t3 T1 Gamma,
    Gamma |- t1 \in Bool ->
    Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1

(* Box Operators *)
| T_Box : forall Delta Gamma t T,
    (Delta, empty) |- t \in T ->
    (Delta, Gamma) |- box t \in □T
| T_Unbox : forall Delta Gamma x t1 t2 T1 T2 ,
    (Delta, Gamma) |- t1 \in ( □T1 ) ->
    (x |-> T1; Delta, Gamma) |- t2 \in T2  ->
    (Delta, Gamma) |- unbox x := t1 in t2 \in T2

(* Dia Operators *)
| T_Dia : forall Delta Gamma t T,
    (Delta, Gamma) |- t \in T ->
    (Delta, Gamma) |- dia t \in ♢T
| T_Undia : forall Delta Gamma x t1 t2 T1 T2 ,
    (Delta, Gamma) |- t1 \in ( ♢T1 ) ->
    (Delta, x |-> T1; Gamma) |- t2 \in T2  ->
    (Delta, Gamma) |- undia x := t1 in t2 \in T2

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

(* All our favorite Modal Axioms: *)

(* λx:A ⊃ B ⊃ C. λy:A ⊃ B. λz:A. (x z) (y z)
   : (A ⊃ B ⊃ C) ⊃(A ⊃ B) ⊃ A ⊃ C *)
Example Modal_Axiom_1 : forall A B C,
   (empty, empty) |- \x:A -> B -> C, \y:A -> B, \z:A, (x z) (y z)
   \in ((A -> B -> C) -> (A -> B) -> A -> C).
Proof.
  repeat econstructor.
Qed.

(* λx:A. λy:B. x
   : A ⊃ B ⊃ A *)
Example Modal_Axiom_2 : forall A B,
    (empty, empty) |- \x : A, \y : B, x \in (A -> B -> A).
Proof.
  repeat econstructor.
Qed.

(* λx:□(A ⊃ B). λy:□A. let box u = x in let box w = y in box (u w)
   : □(A ⊃ B) ⊃(□A ⊃ □B) *)
Example Modal_Axiom_3 : forall A B,
    (empty, empty) |-
      \x:□(A -> B), \y:□A, (unbox u := x in unbox w := y in box (u w))
        \in ((□(A -> B)) -> (□A) -> (□B)).
Proof.
  intros; econstructor.
  econstructor.
  econstructor.
  - repeat econstructor.
  - econstructor.
    + repeat econstructor.
    + econstructor.
      econstructor.
      constructor 2; reflexivity.
      constructor 2; reflexivity.
Qed.

(* λx:□A. let box u = x in u
: □A ⊃ A *)
Example Modal_Axiom_4 : forall A,
    (empty, empty) |- \y : □A, unbox u := y in u \in ((□A) -> A).
Proof.
  econstructor.
  econstructor.
  repeat econstructor.
  econstructor 2; reflexivity.
Qed.

(* λx:□A. let box u = x in box box u
   : □A ⊃ □□A *)
Example Modal_Axiom_5 : forall A,
    (empty, empty) |- \x : □A, unbox u := x in box (box u) \in ((□A) -> (□ (□ A))).
Proof.
  econstructor.
  econstructor.
  repeat econstructor.
  econstructor.
  econstructor.
  econstructor 2; reflexivity.
Qed.

(* λx:A. dia x
   : A ⊃ ♢A *)
Example Modal_Axiom_6 : forall A,
    (empty, empty) |- \x : A, dia x \in (A -> ♢A).
Proof.
  repeat econstructor.
Qed.

(* λx:♢♢A. dia (let dia y = x in let dia z = y in z)
   : ♢♢A ⊃ ♢A *)
Example Modal_Axiom_7 : forall A,
    (empty, empty) |- \x : ♢♢A, dia (undia y := x in undia z := y in z) \in ((♢♢A) -> ♢A).
Proof.
  repeat econstructor.
Qed.

(* λx:□(A ⊃ B). λy:♢A. let box u = x in dia (let dia z = y in u z)
   : □(A ⊃ B) ⊃(♢A ⊃ ♢B) *)
Example Modal_Axiom_8 : forall A B,
    (empty, empty) |- \x : □(A -> B), \y : ♢A, unbox u := x in dia (undia z := y in u z)
                                                                   \in ((□(A -> B)) -> (♢A) -> ♢B).
Proof.
  econstructor.
  econstructor.
  econstructor.
  - repeat econstructor.
  - econstructor.
    econstructor.
    + repeat econstructor.
    + econstructor.
      * econstructor 2; reflexivity.
      * repeat econstructor.
Qed.

Example quote_is_typed (A : ty) :
  let t := quote A in
  (empty, empty) |- t \in ((□A) -> (□□A)).
Proof.
  econstructor.
  econstructor.
  - repeat econstructor.
  - econstructor.
    econstructor.
    econstructor 2; reflexivity.
Qed.

Example apply_is_typed (A B : ty) :
  let t := apply A B in
  (empty, empty) |- t \in ((□A -> B) -> (□A) -> □B).
Proof.
  econstructor.
  econstructor.
  econstructor.
  - repeat econstructor.
  - econstructor.
    + repeat econstructor.
    + econstructor.
      econstructor.
      econstructor 2; reflexivity.
      econstructor 2; reflexivity.
Qed.
