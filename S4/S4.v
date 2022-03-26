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

Fixpoint local_subst (x : string) (s : tm) (t : tm) : tm :=
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
      <{ box t }>
  | <{ unbox y := t1 in t2 }> =>
      if x =? y then <{ unbox y := [x := s] t1 in t2 }>
      else <{ unbox y := [x := s] t1 in [x := s] t2 }>
  (* Diamond operators *)
  | <{ dia t }> =>
      <{ dia ([x := s] t) }>
  | <{ undia y := t1 in t2 }> =>
      if x =? y then <{ undia y := [x := s] t1 in t2 }>
      else <{ undia y := [x := s] t1 in [x := s] t2 }>
  end

where "'[' x ':=' s ']' t" := (local_subst x s t) (in custom stlc_tm).


Reserved Notation "'[[' x ':=' s ']]' t" (in custom stlc_tm at level 20, x constr).

Fixpoint global_subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x =? y then s else t
  | <{\y : T , t1}> =>
      if x =? y then t else <{\y : T, [[x:=s]] t1}>
  | <{t1 t2}> =>
    <{([[x:=s]] t1) ([[x:=s]] t2)}>
  (* Booleans *)
  | <{ true }>  =>
      <{ true }>
  | <{ false }> =>
      <{ false }>
  | <{if t1 then t2 else t3}> =>
      <{if ([[x:=s]] t1) then ([[x:=s]] t2) else ([[x:=s]] t3)}>

  (* Box operators *)
  | <{ box t }> =>
      <{ box [[x:=s]] t }>
  | <{ unbox y := t1 in t2 }> =>
      if x =? y then <{ unbox y := [[x := s]] t1 in t2 }>
      else <{ unbox y := [[x := s]] t1 in [[x := s]] t2 }>
  (* Diamond operators *)
  | <{ dia t }> =>
      <{ dia ([[x := s]] t) }>
  | <{ undia y := t1 in t2 }> =>
      if x =? y then <{ undia y := [[x := s]] t1 in t2 }>
      else <{ undia y := [[x := s]] t1 in [[x := s]] t2 }>
  end

where "'[[' x ':=' s ']]' t" := (global_subst x s t) (in custom stlc_tm).

Reserved Notation "'〈' x ':=' s '〉' t" (in custom stlc_tm at level 20, x constr).

(* This is not the right name... *)
Fixpoint delay (x : string) (s : tm) (t : tm) : tm :=
  match s with
  | <{ undia y := t1 in t2 }> =>
      <{ undia y := t1 in 〈x := t2〉 t }>
  | <{ unbox y := t1 in t2 }> =>
      <{ unbox y := t1 in 〈x := t2〉 t }>
  | s' => <{[x := s']t}>
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
| ST_Unbox1 : forall x t1 t1' t2,
    t1 --> t1' ->
    <{unbox x := t1 in t2}> -->
    <{unbox x := t1' in t2}>
| ST_Unbox : forall x t1 t2,
    <{unbox x := box t1 in t2}> -->
    <{ [[x := t1]]t2 }>

(* Diamond Operator *)
| ST_Dia : forall t1 t1',
    t1 --> t1' ->
    <{ dia t1 }> --> <{ dia t1' }>
| ST_Undia1 : forall x t1 t1' t2,
    t1 --> t1' ->
    <{undia x := t1 in t2}> -->
    <{undia x := t1' in t2}>
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

Inductive var_scope :=
| local : ty -> var_scope
| global : ty -> var_scope.

Definition context := partial_map var_scope.

Definition global_context (Gamma : context) : context :=
  fun x => match Gamma x with
           | Some (global T) => Some (global T)
           | _ => None
           end.

Lemma global_context_OK :
  forall Gamma,
    ((forall x T, Gamma x = Some (global T) -> (global_context Gamma) x = Some (global T)) /\
       (forall x T, (global_context Gamma) x = Some (global T) -> Gamma x = Some (global T)) /\
       (forall x T, (global_context Gamma) x <> Some (local T))).
Proof.
  unfold global_context; intuition; try rewrite H; eauto.
  destruct (Gamma x0) as [ [? | ?] | ]; simpl in *; congruence.
  destruct (Gamma x0) as [ [? | ?] | ]; simpl in *; congruence.
Qed.

Inductive has_type : context -> tm -> ty -> Prop :=
(* Lambda Terms *)
| T_Var1 : forall Gamma x T1,
    Gamma x = Some (local T1) ->
    Gamma |- x \in T1
| T_Var2 : forall Gamma x T1,
    Gamma x = Some (global T1) ->
    Gamma |- x \in T1
| T_Abs : forall Gamma x T1 T2 t1,
    x |-> local T2 ; Gamma |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
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
| T_Box : forall Gamma t T,
    global_context Gamma |- t \in T ->
    Gamma |- box t \in □T
| T_Unbox : forall Gamma x t1 t2 T1 T2 ,
    Gamma |- t1 \in ( □T1 ) ->
    (x |-> global T1; Gamma) |- t2 \in T2  ->
    Gamma |- unbox x := t1 in t2 \in T2

(* Dia Operators *)
| T_Dia : forall Gamma t T,
    has_local_type Gamma t T ->
    Gamma |- dia t \in ♢T

with has_local_type : context -> tm -> ty -> Prop :=
| LT_Undia : forall Gamma x t1 t2 T1 T2 ,
    Gamma |- t1 \in ( ♢T1 ) ->
    has_local_type (x |-> local T1; global_context Gamma) t2 T2  ->
    has_local_type Gamma <{undia x := t1 in t2}> T2
| LT_Unbox : forall Gamma x t1 t2 T1 T2 ,
    Gamma |- t1 \in ( □T1 ) ->
    has_local_type (x |-> global T1; Gamma) t2 T2  ->
    has_local_type Gamma <{unbox x := t1 in t2}> T2
| LT_global : forall Gamma t T,
    Gamma |- t \in T ->
    has_local_type Gamma t T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Scheme has_type_ind' := Induction for has_type Sort Prop
  with has_local_type_ind' := Induction for has_local_type Sort Prop.

(* All our favorite Modal Axioms: *)

(* λx:A ⊃ B ⊃ C. λy:A ⊃ B. λz:A. (x z) (y z)
   : (A ⊃ B ⊃ C) ⊃(A ⊃ B) ⊃ A ⊃ C *)
Example Modal_Axiom_1 : forall A B C,
   empty |- \x:A -> B -> C, \y:A -> B, \z:A, (x z) (y z)
   \in ((A -> B -> C) -> (A -> B) -> A -> C).
Proof.
  repeat econstructor.
Qed.

(* λx:A. λy:B. x
   : A ⊃ B ⊃ A *)
Example Modal_Axiom_2 : forall A B,
    empty |- \x : A, \y : B, x \in (A -> B -> A).
Proof.
  repeat econstructor.
Qed.

(* λx:□(A ⊃ B). λy:□A. let box u = x in let box w = y in box (u w)
   : □(A ⊃ B) ⊃(□A ⊃ □B) *)
Example Modal_Axiom_3 : forall A B,
    empty |-
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
    empty |- \y : □A, unbox u := y in u \in ((□A) -> A).
Proof.
  econstructor.
  econstructor.
  repeat econstructor.
  econstructor 2; reflexivity.
Qed.

(* λx:□A. let box u = x in box box u
   : □A ⊃ □□A *)
Example Modal_Axiom_5 : forall A,
    empty |- \x : □A, unbox u := x in box (box u) \in ((□A) -> (□ (□ A))).
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
    empty |- \x : A, dia x \in (A -> ♢A).
Proof.
  repeat econstructor.
Qed.

(* λx:♢♢A. dia (let dia y = x in let dia z = y in z)
   : ♢♢A ⊃ ♢A *)
Example Modal_Axiom_7 : forall A,
    empty |- \x : ♢♢A, dia (undia y := x in undia z := y in z) \in ((♢♢A) -> ♢A).
Proof.
  repeat econstructor.
Qed.

(* λx:□(A ⊃ B). λy:♢A. let box u = x in dia (let dia z = y in u z)
   : □(A ⊃ B) ⊃(♢A ⊃ ♢B) *)
Example Modal_Axiom_8 : forall A B,
    empty |- \x : □(A -> B), \y : ♢A, unbox u := x in dia (undia z := y in u z)
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
      econstructor.
      * econstructor 2; reflexivity.
      * repeat econstructor.
Qed.

(* λx: A ⊃ B. λy:♢A. let box u = x in dia (let dia z = y in u z)
   : (A ⊃ B) ⊃(♢A ⊃ ♢B) *)
Example Modal_Axiom_8' : forall A B,
    ~ (empty |- \x : A -> B, \y : ♢A, dia (undia z := y in x z) \in (((A -> B)) -> (♢A) -> ♢B)).
Proof.
  unfold not; intros.
  inversion H; subst; clear H.
  inversion H2; subst; clear H2.
  inversion H1; subst; clear H1.
  inversion H3; subst; clear H3.
  - inversion H6; subst; clear H6.
    inversion H; subst; clear H.
    inversion H3; subst; clear H3.
    compute in H1; discriminate.
    compute in H1; discriminate.
  - inversion H.
Qed.

Example quote_is_typed (A : ty) :
  let t := quote A in
  empty |- t \in ((□A) -> (□□A)).
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
  empty |- t \in ((□A -> B) -> (□A) -> □B).
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

Hint Constructors has_type.

Lemma canonical_forms_bool : forall t,
  empty |- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto; inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal; inversion HT; subst; eauto.
Qed.

Lemma canonical_forms_box : forall t T,
  empty |- t \in (□ T) ->
  value t ->
  exists u, t = <{box u}>.
Proof.
  intros t T HT HVal.
  destruct HVal; auto; inversion HT; subst; eauto.
Qed.

Lemma canonical_forms_diamond : forall t T,
  empty |- t \in (♢ T) ->
  value t ->
  exists u, t = <{dia u}>.
Proof.
  intros t T HT HVal.
  destruct HVal; auto; inversion HT; subst; eauto.
Qed.

Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; try injection HeqGamma; intros; subst;
    try discriminate; try solve [left; constructor].
  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; [|assumption].
        destruct Ht1 as [x [t0 H1] ]. subst.
        exists (<{ [x:=t2]t0 }>).
        econstructor; eauto.
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>).
        econstructor 3; eauto.
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{t1' t2}>)...
      econstructor; eauto.
  - (* T_If *)
    right. destruct IHHt1...

    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.
      * exists t2; econstructor; eauto.
      * exists t3; econstructor; eauto.
    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists <{if t1' then t2 else t3}>...
      econstructor; eauto.
  - (* T_Box *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct (canonical_forms_box t1 T1); subst; eauto.
      * eexists; econstructor 9.
    + destruct H as [t1' Hstp].
      eexists; econstructor; eauto.
Qed.

Lemma inclusion_global_context :
  forall Gamma Gamma',
    inclusion Gamma Gamma' ->
    inclusion (global_context Gamma) (global_context Gamma').
Proof.
  unfold global_context, inclusion; intros.
  destruct (Gamma x0) eqn: ?.
  - erewrite H; eauto.
  - discriminate.
Qed.

Lemma inclusion_global_context_local_update :
  forall x T T' Gamma,
    inclusion (x |-> T; (global_context (x |-> T'; Gamma))) (x |-> T; global_context Gamma).
Proof.
  unfold global_context, inclusion; intros.
  unfold update, t_update in *.
  destruct (eqb_string x0 x1) eqn: ?; try discriminate; congruence.
Qed.

Lemma weakening : forall Gamma Gamma' t T,
    inclusion Gamma Gamma' ->
    Gamma  |- t \in T  -> Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T HInc Ht;
    revert Gamma' HInc.
  pattern Gamma, t, T, Ht;
    eapply has_type_ind' with
    (P := fun Gamma t T _ => forall Gamma' : partial_map var_scope, inclusion Gamma Gamma' -> Gamma' |- t \in T)
    (P0 := fun Gamma t T _ => forall Gamma' : partial_map var_scope, inclusion Gamma Gamma' -> has_local_type Gamma' t T); eauto using inclusion_update; clear; intros.
  - econstructor.
    eapply H; eauto; compute; eauto.
    unfold inclusion in H0.
    intros; specialize (H0 x0 v); destruct (Gamma x0) as [ [? | ?] | ]; try congruence.
    rewrite H0; injection H1; intros; subst; congruence.
  - econstructor; eauto.
    eapply H0; eauto using inclusion_update, inclusion_global_context.
  - econstructor; eauto using inclusion_update.
  - econstructor; eauto.
Qed.

Lemma local_weakening : forall Gamma Gamma' t T,
    inclusion Gamma Gamma' ->
    has_local_type Gamma t T  -> has_local_type Gamma' t T.
Proof.
  intros Gamma Gamma' t T HInc Ht;
    revert Gamma' HInc;
    induction Ht; simpl; intros;
    econstructor; eauto using weakening, inclusion_update, inclusion_global_context.
Qed.

Lemma local_substitution_preserves_typing
  : forall Gamma x U t v T,
  (x |-> local U; Gamma) |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht.
  remember (x |-> local U; Gamma) as Gamma'.
  assert (inclusion Gamma'  (x |-> local U; Gamma)) by
    (rewrite HeqGamma'; unfold inclusion; congruence).
  clear HeqGamma'.
  generalize dependent Gamma.
  pattern Gamma', t, T, Ht;
    eapply has_type_ind' with
    (P := fun Gamma' t T _ =>
            forall
              (Gamma : partial_map var_scope)
              (Heq : inclusion Gamma' (x |-> local U; Gamma))
              (Hv : empty |- v \in U),
              Gamma |- [x := v] t \in T)
    (P0 := fun Gamma' t T _ =>
             forall
               (Gamma : partial_map var_scope)
               (Heq : inclusion Gamma' (x |-> local U; Gamma))
               (Hv : empty |- v \in U),
               has_local_type Gamma (<{[x := v] t}>) T);
    eauto using inclusion_update; clear; intros; subst; simpl; eauto.
  - (* var1 *)
    rename x0 into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      eapply Heq in e; rewrite update_eq in e.
      injection e as H2; subst.
      rewrite eqb_refl; intros; eapply weakening; try eassumption;
        unfold inclusion; eauto.
      compute; congruence.
    + (* x<>y *)
      apply Heq in e.
      rewrite (proj2 (eqb_neq x y)); eauto.
      intros; apply T_Var1.
      rewrite update_neq in e; auto.
  - rename x0 into y. destruct (eqb_stringP x y); eapply Heq in e; subst.
    + (* x=y *)
      rewrite update_eq in e; congruence.
    + (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      intros; apply T_Var2. rewrite update_neq in e; auto.
  - (* abs *)
    rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      apply T_Abs.
      eapply weakening; try eassumption.
      admit.
      (*rewrite update_shadow in h. assumption. *)
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      apply T_Abs.
      apply H; eauto.
      rewrite update_permute; auto using inclusion_update.
  - (* box *)
    econstructor.
    eapply weakening; try eassumption.
    admit.
    (*unfold inclusion; simpl; intros.
    unfold update, t_update, global_context in *|-*.
    destruct (eqb_stringP x x0); subst; eauto.
    congruence. *)
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      admit.
      (*rewrite update_shadow in h0.
      econstructor; eauto. *)
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply T_Unbox.
      * apply H; eauto.
      * eapply H0; eauto.
        rewrite update_permute; auto using inclusion_update.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      econstructor; eauto.
      admit.
      (*eapply local_weakening; eauto using inclusion_update, inclusion_global_context_local_update. *)
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply LT_Undia.
      * apply H; eauto.
      * eapply H0; eauto.
        rewrite update_permute by congruence.
        eapply inclusion_update.
        apply inclusion_global_context in Heq.
        admit.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      admit.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply LT_Unbox.
      * apply H; eauto.
      * eapply H0; eauto.
        rewrite update_permute; auto.
        admit.
  - econstructor; eauto.
Admitted.

Inductive bound_in : string -> tm -> Prop :=
  | bi_app1 : forall x t1 t2,
      bound_in x t1 -> bound_in x <{ t1 t2 }>
  | bi_app2 : forall x t1 t2,
      bound_in x t2 -> bound_in x <{ t1 t2 }>
| bi_abs : forall x T11 t12,
    bound_in x <{ \x : T11, t12 }>
| bi_abs2 : forall x y T11 t12,
    bound_in x <{ t12 }> ->
    bound_in x <{ \y : T11, t12 }>

  (* booleans *)
  | bi_test0 : forall x t0 t1 t2,
      bound_in x t0 ->
      bound_in x <{ if t0 then t1 else t2 }>
  | bi_test1 : forall x t0 t1 t2,
      bound_in x t1 ->
      bound_in x <{ if t0 then t1 else t2 }>
  | bi_test2 : forall x t0 t1 t2,
      bound_in x t2 ->
      bound_in x <{ if t0 then t1 else t2 }>
  (* Modal Operators  *)
  | bi_box : forall x t1,
      bound_in x t1 ->
      bound_in x <{ box t1 }>
| bi_unbox1 : forall x t1 t2,
    bound_in x <{ unbox x := t1 in t2 }>
| bi_unbox2 : forall x y t1 t2,
      bound_in x t1 ->
      bound_in x <{ unbox y := t1 in t2 }>
| bi_unbox3 : forall x y t1 t2,
    bound_in x t2 ->
    bound_in x <{ unbox y := t1 in t2 }>

| bi_dia : forall x t1,
      bound_in x t1 ->
      bound_in x <{ dia t1 }>
| bi_undia1 : forall x t1 t2,
      bound_in x <{ undia x := t1 in t2 }>
| bi_undia2 : forall x y t1 t2,
      bound_in x t1 ->
      bound_in x <{ undia y := t1 in t2 }>
| bi_undia3 : forall x y t1 t2,
    bound_in x t2 ->
    bound_in x <{ undia y := t1 in t2 }>.

Hint Constructors bound_in : core.

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall (x : string),
      appears_free_in x <{ x }>
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x <{ t1 t2 }>
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x <{ t1 t2 }>
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x <{ \y : T11, t12 }>

  (* booleans *)
  | afi_test0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  | afi_test2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ if t0 then t1 else t2 }>
  (* Modal Operators  *)
  | afi_box : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x <{ box t1 }>
| afi_unbox1 : forall x y t1 t2,
    appears_free_in x t2 ->
    appears_free_in x <{ unbox y := t1 in t2 }>
| afi_unbox2 : forall x y t1 t2,
    x <> y ->
    appears_free_in x t2 ->
    appears_free_in x <{ unbox y := t1 in t2 }>
| afi_dia : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x <{ dia t1 }>
  | afi_undia1 : forall x y t1 t2,
      appears_free_in x t2 ->
      appears_free_in x <{ undia y := t1 in t2 }>
| afi_undia2 : forall x y t1 t2,
    x <> y ->
    appears_free_in x t2 ->
    appears_free_in x <{ undia y := t1 in t2 }>.

Hint Constructors appears_free_in : core.

Lemma inclusion_update_empty
  : forall x T (Gamma : context),
    inclusion (x |-> T) (x |-> T; Gamma).
Proof.
  unfold inclusion, update, t_update;
    intros; destruct (eqb_stringP x0 x1); subst; eauto.
  discriminate.
Qed.

Lemma local_substitution_preserves_typing'
  : forall Gamma Gamma'' x U t v T
           (Hx : forall x, bound_in x t -> Gamma'' x = None)
           (HInc : inclusion Gamma'' Gamma),
  (x |-> local U; Gamma) |- t \in T ->
  Gamma'' |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma Gamma'' x U t v T Hx HInc Ht.
  remember (x |-> local U; Gamma) as Gamma'.
  revert Hx HInc.
  generalize dependent Gamma.
  revert Gamma''.
  pattern Gamma', t, T, Ht;
    eapply has_type_ind' with
    (P := fun Gamma' t T _ =>
            forall
              (Gamma'' Gamma : partial_map var_scope)
              (Heq : Gamma' = (x |-> local U; Gamma))
              (Hx : forall x, bound_in x t -> Gamma'' x = None)
              (HInc : inclusion Gamma'' Gamma)
              (Hv : Gamma'' |- v \in U),
              Gamma |- [x := v] t \in T)
    (P0 := fun Gamma' t T _ =>
             forall
               (Gamma'' Gamma : partial_map var_scope)
               (Heq : Gamma' = (x |-> local U; Gamma))
               (Hx : forall x, bound_in x t -> Gamma'' x = None)
               (HInc : inclusion Gamma'' Gamma)
               (Hv : Gamma'' |- v \in U),
               has_local_type Gamma (<{[x := v] t}>) T);
    eauto using inclusion_update; clear; intros; subst; simpl; eauto.
  - (* var1 *)
    rename x0 into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in e.
      injection e as H2; subst.
      rewrite eqb_refl; intros; eapply weakening; try eassumption;
        unfold inclusion; eauto.
    + (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      intros; apply T_Var1. rewrite update_neq in e; auto.
  - rename x0 into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in e; congruence.
    + (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      intros; apply T_Var2. rewrite update_neq in e; auto.
  - (* abs *)
    rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      apply T_Abs.
      rewrite update_shadow in h. assumption.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      apply T_Abs.
      eapply H with (Gamma'' := Gamma''); eauto.
      rewrite update_permute; auto.
      * unfold inclusion, update, t_update.
        intros; destruct (eqb_stringP y x0); subst; eauto.
        rewrite Hx in H0; try discriminate; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - (* box *)
    econstructor.
    eapply weakening; try eassumption.
    unfold inclusion; simpl; intros.
    unfold update, t_update, global_context in *|-*.
    destruct (eqb_stringP x x0); subst; eauto.
    congruence.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in h0.
      econstructor; eauto.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply T_Unbox.
      * eapply H; eauto.
      * eapply H0; eauto.
        rewrite update_permute; auto.
        unfold inclusion; simpl; intros.
        unfold update, t_update, global_context.
        destruct (eqb_stringP y x0); subst; eauto.
        rewrite Hx in H1; eauto; try discriminate.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      econstructor; eauto using local_weakening, inclusion_update, inclusion_global_context_local_update.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      admit.
      (* eapply LT_Undia. *)
      (* * eapply H; eauto. *)
      (* * eapply H0; eauto. *)
      (*   rewrite update_permute; auto. *)
      (*   unfold inclusion, update, t_update, global_context; intros. *)
      (*   destruct (eqb_stringP y x0); subst; eauto. *)
      (*   rewrite Hx in H1; eauto; try discriminate. *)
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in h0.
      econstructor; eauto.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply LT_Unbox.
      * eapply H; eauto.
      * eapply H0; eauto.
        rewrite update_permute; auto.
        unfold inclusion, update, t_update, global_context; intros.
        destruct (eqb_stringP y x0); subst; eauto.
        rewrite Hx in H1; eauto; try discriminate.
  - econstructor; eauto.
Admitted.

Lemma local_substitution_preserves_local_typing'
  : forall Gamma Gamma'' x U t v T
           (Hx : forall x, bound_in x t -> Gamma'' x = None)
           (HInc : inclusion Gamma'' Gamma),
    has_local_type (x |-> local U; Gamma) t  T ->
    Gamma'' |- v \in U ->
    has_local_type Gamma <{[x:=v]t}> T.
Proof.
  intros Gamma Gamma'' x U t v T Hx HInc Ht.
  remember (x |-> local U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros; simpl.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      econstructor; eauto using local_substitution_preserves_typing'.
      eapply local_weakening; eauto using inclusion_global_context_local_update,
        inclusion_update.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply LT_Undia; eauto using local_substitution_preserves_typing'.
      admit.
      (* eapply IHHt; eauto using local_substitution_preserves_typing'.
      * unfold inclusion, update, t_update, global_context; intros.
        destruct (eqb_stringP y x0); subst; eauto.
        rewrite Hx in H1; eauto; try discriminate.
      * rewrite update_permute; auto. *)
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in Ht.
      econstructor; eauto using local_substitution_preserves_typing'.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply LT_Unbox; eauto using local_substitution_preserves_typing'.
      eapply IHHt; eauto using local_substitution_preserves_typing'.
      * unfold inclusion, update, t_update, global_context; intros.
        destruct (eqb_stringP y x0); subst; eauto.
        rewrite Hx in H1; eauto; try discriminate.
      * rewrite update_permute; auto.
  - subst; econstructor; eauto using local_substitution_preserves_typing'.
Admitted.

(*Theorem local_substitution_preserves_local_typing : forall Gamma x U t v T,
    has_local_type (x |-> local U; Gamma) t T ->
    empty |- v \in U   ->
  has_local_type Gamma <{[x:=v]t}> T.
Proof.
  intros Gamma x U t v T Ht.
  remember (x |-> local U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros; subst; simpl; eauto.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in Ht.
      econstructor; eauto.
      eapply local_substitution_preserves_typing; try eassumption.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      econstructor.
      * eapply local_substitution_preserves_typing;
          try eassumption; try reflexivity; discriminate.
      * eapply IHHt; eauto.
        rewrite update_permute; auto.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in Ht.
      econstructor; eauto.
      eapply local_substitution_preserves_typing;
        try eassumption; try reflexivity; discriminate.
    + rewrite (proj2 (eqb_neq x y)); eauto.
      econstructor; eauto using local_substitution_preserves_typing;
        try eassumption; try reflexivity; try discriminate.
      eapply IHHt; eauto.
      rewrite update_permute; auto.
  - econstructor; eauto using local_substitution_preserves_typing.
Qed. *)

Lemma global_substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> global U; Gamma) |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [[x:=v]]t \in T.
Proof.
  intros Gamma x U t v T Ht.
  remember (x |-> global U; Gamma) as Gamma'.
  generalize dependent Gamma.
  pattern Gamma', t, T, Ht;
    eapply has_type_ind' with
    (P := fun Gamma' t T _ =>
            forall
              (Gamma : partial_map var_scope)
              (Heq : Gamma' = (x |-> global U; Gamma))
                   (Hv : empty |- v \in U),
              Gamma |- [[x := v]] t \in T)
    (P0 := fun Gamma' t T _ =>
             forall
               (HId : has_local_type Gamma' t T)
               (Gamma : partial_map var_scope)
                    (Heq : Gamma' = (x |-> global U; Gamma))
                    (Hv : empty |- v \in U),
               has_local_type Gamma (<{[[x := v]] t}>) T);
    eauto using inclusion_update; clear; intros; subst; simpl; eauto.
  - (* var1 *)
    rename x0 into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in e.
      injection e as H2; subst.
      rewrite eqb_refl; intros; eapply weakening; try eassumption;
        unfold inclusion; eauto.
      compute; discriminate.
    + (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      intros; apply T_Var1. rewrite update_neq in e; auto.
  - rename x0 into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_eq in e; injection e; intros; subst.
      eapply weakening; eauto.
      compute; congruence.
    + (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      intros; apply T_Var2. rewrite update_neq in e; auto.
  - (* abs *)
    rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      apply T_Abs.
      rewrite update_shadow in h. assumption.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      apply T_Abs.
      apply H; eauto.
      rewrite update_permute; auto.
  - (* box *)
    econstructor.
    eapply H; eauto.
    eapply functional_extensionality; intros.
    unfold update, t_update, global_context in *|-*.
    destruct (eqb_stringP x x0); subst; eauto.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in h0.
      econstructor; eauto.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply T_Unbox.
      * apply H; eauto.
      * eapply H0; eauto.
        rewrite update_permute; auto.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      econstructor; eauto.
      eapply local_weakening; eauto using inclusion_global_context_local_update,
        inclusion_update.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply LT_Undia.
      * apply H; eauto.
      * eapply H0; eauto.
        rewrite update_permute by congruence.
        f_equal.
        apply functional_extensionality; intros.
        unfold global_context, update, t_update.
        destruct (eqb_string x x0) eqn: ?; eauto.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in h0.
      econstructor; eauto.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      eapply LT_Unbox.
      * apply H; eauto.
      * eapply H0; eauto.
        rewrite update_permute; auto.
  - econstructor; eauto.
Qed.

Theorem global_substitution_preserves_local_typing : forall Gamma x U t v T,
    has_local_type (x |-> global U; Gamma) t T ->
  empty |- v \in U   ->
  has_local_type Gamma <{[[x:=v]]t}> T.
Proof.
  intros Gamma x U t v T Ht.
  remember (x |-> global U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros; subst; simpl; eauto.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      econstructor; eauto using global_substitution_preserves_typing.
      eapply local_weakening; eauto using inclusion_global_context_local_update.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      econstructor; eauto using global_substitution_preserves_typing.
      eapply IHHt; eauto.
      rewrite update_permute; auto.
      f_equal.
      apply functional_extensionality; intros.
      unfold global_context, update, t_update.
      destruct (eqb_string x x0) eqn: ?; eauto.
  - rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in Ht.
      econstructor; eauto using global_substitution_preserves_typing.
    + rewrite (proj2 (eqb_neq x y)); eauto.
      econstructor; eauto using global_substitution_preserves_typing.
      eapply IHHt; eauto.
      rewrite update_permute; auto.
  - econstructor; eauto using global_substitution_preserves_typing.
Qed.

Definition disjoint_contexts (Gamma Gamma' : context) : Prop :=
  (forall x T, Gamma x = Some T -> Gamma' x = None) /\
    (forall x T, Gamma' x = Some T -> Gamma x = None).

Definition union_contexts (Gamma Gamma' : context) : context :=
  fun x => match Gamma x with
           | Some T => Some T
           | _ => Gamma' x
           end.

Lemma union_empty : forall (Gamma : context),
    union_contexts Gamma empty = Gamma.
Proof.
  intros; apply functional_extensionality.
  intros; unfold union_contexts; destruct (Gamma x0); eauto.
Qed.

Lemma disjoint_empty : forall (Gamma : context),
    disjoint_contexts Gamma empty.
Proof.
  unfold disjoint_contexts; split; simpl; intros.
  reflexivity.
  discriminate.
Qed.

Lemma inclusion_union : forall (Gamma Gamma' : context),
    inclusion Gamma (union_contexts Gamma Gamma').
Proof.
  unfold inclusion, union_contexts; intros.
  destruct (Gamma x0); congruence.
Qed.

Lemma lookup_disjoint_contexts
      : forall (Gamma Gamma' : context),
      disjoint_contexts Gamma Gamma' ->
      forall x T, Gamma' x = Some T ->
                  (union_contexts Gamma Gamma') x = Some T.
Proof.
  unfold union_contexts; intros.
  unfold disjoint_contexts in H; intuition.
  specialize (H1 x0).
  destruct (Gamma x0); eauto.
  erewrite H1 in H0; try discriminate; reflexivity.
Qed.

Lemma inclusion_union_2 : forall (Gamma Gamma' : context),
    disjoint_contexts Gamma Gamma' ->
    inclusion Gamma' (union_contexts Gamma Gamma').
Proof.
  unfold inclusion; intros.
  eauto using lookup_disjoint_contexts.
Qed.

Lemma local_substitution_preserves_local_typing''
  : forall Gamma Gamma'' x U t v T
           (Hx : forall x, bound_in x t -> ~ bound_in x v)
           (HInc : disjoint_contexts Gamma'' Gamma),
    has_local_type (x |-> local U; Gamma) t  T ->
    Gamma'' |- v \in U ->
    has_local_type (union_contexts Gamma'' Gamma) <{[x:=v]t}> T.
Proof.
Admitted.

Lemma delaying_preserves_local_typing
  : forall Gamma x U t v T
           (NIn_x : Gamma x = None)
           (NIn_x_2 : ~ bound_in x v)
           (Hx : forall x, bound_in x t -> ~ bound_in x v),
    has_local_type (x |-> local U) t T ->
    has_local_type Gamma v U   ->
    has_local_type Gamma <{〈 x := v〉t}> T.
Proof.
  intros Gamma x U t v T NIn_x NIn_x2 Hx Ht He.
  revert NIn_x2 NIn_x Hx.
  generalize dependent T.
  pattern Gamma, v, U, He.
    eapply has_local_type_ind' with
      (P := (fun (o : context) (t0 : tm) (t1 : ty) (_ : has_type o t0 t1) =>
               forall (T : ty),
                 has_local_type (x |-> local t1) t T ->
                 (~ bound_in x t0) ->
                 (o x = None ) ->
                 (forall x, bound_in x t -> ~ bound_in x t0) ->
                 has_local_type o <{ 〈 x := t0〉  t }> T))
      (P0 := (fun (o : context) (t0 : tm) (t1 : ty) (_ : has_local_type o t0 t1) =>
               forall (T : ty),
                 has_local_type (x |-> local t1) t T ->
                 (~ bound_in x t0) ->
                 (o x = None) ->
                 (forall x, bound_in x t -> ~ bound_in x t0) ->
                   has_local_type o <{ 〈 x := t0 〉 t }> T));
      try solve [simpl; intros;
                 rewrite <- (union_empty Gamma0);
                 eapply local_substitution_preserves_local_typing'';
                 unfold inclusion; eauto using local_weakening, inclusion_update_empty, disjoint_empty];
      eauto.
  - simpl; econstructor; eauto.
    eapply H0; eauto using inclusion_update.
    + unfold update, t_update; simpl.
      destruct (eqb_stringP x0 x); subst; eauto.
      destruct H2; eauto.
    + unfold not; intros.
      eapply H4; eauto.
  - simpl; econstructor; eauto.
    eapply H0; eauto using inclusion_update.
    + unfold update, t_update; simpl.
      destruct (eqb_stringP x0 x); subst; eauto.
      destruct H2; eauto.
      unfold global_context; rewrite H3; reflexivity.
    + unfold not; intros.
      eapply H4; eauto.
  - simpl; econstructor; eauto.
    eapply H0; eauto using inclusion_update.
    + unfold update, t_update; simpl.
      destruct (eqb_stringP x0 x); subst; eauto.
      destruct H2; eauto.
    + unfold not; intros.
      eapply H4; eauto.
Qed.

(* Alas, it appears that we cannot escape variable renaming :p *)

Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t --> t'  ->
  empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  eapply has_type_ind' with
    (P := fun Gamma t T _ => Gamma = empty ->  forall (t' : tm) (HE : t --> t'), Gamma |- t' \in T)
    (P0 := fun Gamma t T _ =>  Gamma = empty ->  forall (t' : tm) (HE : t --> t'), has_local_type Gamma t' T)
    in HT; eauto; clear; intros; subst; try discriminate;
    try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    + eapply local_substitution_preserves_typing with T2; eauto.
      inversion h; subst; eauto.
  - inversion HE; subst...
    eapply global_substitution_preserves_typing with T1; eauto.
    inversion h; eauto.
  - inversion HE; subst...
    + econstructor; eauto.
    + inversion h; subst.
      eapply delaying_preserves_local_typing; try eassumption.
      reflexivity.
      admit.
      admit.
  - inversion HE; subst...
    + econstructor; eauto.
    + eapply global_substitution_preserves_local_typing; eauto.
      inversion h; subst; assumption.
  - econstructor; eauto.
Admitted.
