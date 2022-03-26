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
| local_var : string -> tm
| tm_app    : tm -> tm -> tm
| tm_abs    : string -> ty -> tm -> tm
(* Booleans *)
| tm_true   : tm
| tm_false  : tm
| tm_if     : tm -> tm -> tm -> tm
(* Box operators *)
| global_var : string -> tm
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

Definition LocalVar := string.
Definition  LiftLocalVar : LocalVar -> tm := local_var.
Coercion  LiftLocalVar : LocalVar >-> tm.

Definition GlobalVar := string.
Definition LiftGlobalVar : GlobalVar -> tm := global_var.
Coercion  LiftGlobalVar : GlobalVar >-> tm.

Definition x : LocalVar := "x".
Definition y : LocalVar := "y".
Definition z : LocalVar := "z".
Definition f : LocalVar := "f".
Definition g : LocalVar := "g".

Definition u : GlobalVar := "u".
Definition w : GlobalVar := "w".
Definition t : GlobalVar := "t".
Definition s : GlobalVar := "s".

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
  | local_var y =>
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
  | global_var u => global_var u
  | <{ box t }> =>
      <{ box t }>
  | <{ unbox y := t1 in t2 }> =>
      <{ unbox y := [x := s] t1 in [x := s] t2 }>
  (* Diamond operators *)
  | <{ dia t }> =>
      <{ dia ([x := s] t) }>
  | <{ undia y := t1 in t2 }> =>
      (*if x =? y then  *)
       <{ undia y := [x := s] t1 in t2 }>
      (*else <{ undia y := [x := s] t1 in [x := s] t2 }> *)
  end

where "'[' x ':=' s ']' t" := (local_subst x s t) (in custom stlc_tm).

Reserved Notation "'[[' x ':=' s ']]' t" (in custom stlc_tm at level 20, x constr).

Fixpoint global_subst (u : string) (s : tm) (t : tm) : tm :=
  match t with
  | local_var y => local_var y
  | <{\y : T , t1}> => <{\y : T, [[u:=s]] t1}>
  | <{t1 t2}> =>
    <{([[u:=s]] t1) ([[u:=s]] t2)}>
  (* Booleans *)
  | <{ true }>  =>
      <{ true }>
  | <{ false }> =>
      <{ false }>
  | <{if t1 then t2 else t3}> =>
      <{if ([[u:=s]] t1) then ([[u:=s]] t2) else ([[u:=s]] t3)}>

  (* Box operators *)
  | global_var v =>
      if u =? v then s else t
  | <{ box t }> =>
      <{ box [[u:=s]] t }>
  | <{ unbox y := t1 in t2 }> =>
      if u =? y then <{ unbox y := [[u := s]] t1 in t2 }>
      else <{ unbox y := [[u := s]] t1 in [[u := s]] t2 }>
  (* Diamond operators *)
  | <{ dia t }> =>
      <{ dia ([[u := s]] t) }>
  | <{ undia y := t1 in t2 }> =>
      <{ undia y := [[u := s]] t1 in [[u := s]] t2 }>
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

Reserved Notation "Delta ';;' Gamma '|-' t '\in' T"
            (at level 101,
             t custom stlc_tm, T custom stlc_ty at level 0).

Definition context := partial_map ty.

Inductive has_type : context -> context -> tm -> ty -> Prop :=
(* Lambda Terms *)
| T_Local_Var : forall Delta Gamma x T1,
    Gamma x = Some T1 ->
    has_type Delta Gamma (local_var x) T1
| T_Abs : forall Delta Gamma x T1 T2 t1,
    Delta;;  x |-> T2 ; Gamma |- t1 \in T1 ->
    Delta;; Gamma |- \x:T2, t1 \in (T2 -> T1)
| T_App : forall Delta Gamma T1 T2 t1 t2,
      Delta;; Gamma |- t1 \in (T2 -> T1) ->
      Delta;; Gamma |- t2 \in T2 ->
      Delta;; Gamma |- t1 t2 \in T1

(* Booleans *)
| T_True : forall Delta Gamma,
      Delta ;; Gamma |- true \in Bool
| T_False : forall Delta Gamma,
       Delta;; Gamma |- false \in Bool
| T_If : forall Delta Gamma t1 t2 t3 T1,
    Delta;; Gamma |- t1 \in Bool ->
    Delta;; Gamma |- t2 \in T1 ->
       Delta;; Gamma |- t3 \in T1 ->
       Delta;; Gamma |- if t1 then t2 else t3 \in T1

(* Box Operators *)
| T_Global_Var : forall Delta Gamma u T1,
    Delta u = Some T1 ->
    has_type Delta Gamma (global_var u) T1
| T_Box : forall Delta Gamma t T,
    Delta;; empty  |- t \in T ->
    Delta;; Gamma |- box t \in □T
| T_Unbox : forall Delta Gamma x t1 t2 T1 T2 ,
    Delta;; Gamma |- t1 \in ( □T1 ) ->
    (x |-> T1; Delta) ;; Gamma |- t2 \in T2  ->
    Delta;; Gamma |- unbox x := t1 in t2 \in T2

(* Dia Operators *)
| T_Dia : forall Delta Gamma t T,
    has_local_type Delta Gamma t T ->
    Delta;; Gamma |- dia t \in ♢T

with has_local_type : context -> context -> tm -> ty -> Prop :=
| LT_Undia : forall Delta Gamma x t1 t2 T1 T2 ,
    Delta;; Gamma |- t1 \in ( ♢T1 ) ->
    has_local_type Delta (x |-> T1; empty) t2 T2  ->
    has_local_type Delta Gamma <{undia x := t1 in t2}> T2
| LT_Unbox : forall Delta Gamma x t1 t2 T1 T2 ,
    Delta;; Gamma |- t1 \in ( □T1 ) ->
    has_local_type (x |-> T1; Delta) Gamma t2 T2  ->
    has_local_type Delta Gamma <{unbox x := t1 in t2}> T2
| LT_global : forall Delta Gamma t T,
    Delta;; Gamma |- t \in T ->
    has_local_type Delta Gamma t T

where "Delta ';;' Gamma '|-' t '\in' T" := (has_type Delta Gamma t T).

Scheme has_type_ind' := Induction for has_type Sort Prop
  with has_local_type_ind' := Induction for has_local_type Sort Prop.

(* All our favorite Modal Axioms: *)

(* λx:A ⊃ B ⊃ C. λy:A ⊃ B. λz:A. (x z) (y z)
   : (A ⊃ B ⊃ C) ⊃(A ⊃ B) ⊃ A ⊃ C *)
Example Modal_Axiom_1 : forall A B C,
   empty;; empty |- \x:A -> B -> C, \y:A -> B, \z:A, (x z) (y z)
   \in ((A -> B -> C) -> (A -> B) -> A -> C).
Proof.
  repeat econstructor.
Qed.

(* λx:A. λy:B. x
   : A ⊃ B ⊃ A *)
Example Modal_Axiom_2 : forall A B,
    empty;; empty |- \x : A, \y : B, x \in (A -> B -> A).
Proof.
  repeat econstructor.
Qed.

(* λx:□(A ⊃ B). λy:□A. let box u = x in let box w = y in box (u w)
   : □(A ⊃ B) ⊃(□A ⊃ □B) *)
Example Modal_Axiom_3 : forall A B,
    empty;; empty |-
      \x:□(A -> B), \y:□A, (unbox u := x in unbox w := y in box (u w))
        \in ((□(A -> B)) -> (□A) -> (□B)).
Proof.
  intros; repeat econstructor.
Qed.

(* λx:□A. let box u = x in u
: □A ⊃ A *)
Example Modal_Axiom_4 : forall A,
    empty;; empty |- \y : □A, unbox u := y in u \in ((□A) -> A).
Proof.
  repeat econstructor.
Qed.

(* λx:□A. let box u = x in box box u
   : □A ⊃ □□A *)
Example Modal_Axiom_5 : forall A,
    empty;; empty |- \x : □A, unbox u := x in box (box u) \in ((□A) -> (□ (□ A))).
Proof.
  repeat econstructor.
Qed.

(* λx:A. dia x
   : A ⊃ ♢A *)
Example Modal_Axiom_6 : forall A,
    empty;; empty |- \x : A, dia x \in (A -> ♢A).
Proof.
  repeat econstructor.
Qed.

(* λx:♢♢A. dia (let dia y = x in let dia z = y in z)
   : ♢♢A ⊃ ♢A *)
Example Modal_Axiom_7 : forall A,
    empty;; empty |- \x : ♢♢A, dia (undia y := x in undia z := y in z) \in ((♢♢A) -> ♢A).
Proof.
  repeat econstructor.
Qed.

(* λx:□(A ⊃ B). λy:♢A. let box u = x in dia (let dia z = y in u z)
   : □(A ⊃ B) ⊃(♢A ⊃ ♢B) *)
Example Modal_Axiom_8 : forall A B,
    empty;; empty |- \x : □(A -> B), \y : ♢A, unbox u := x in dia (undia z := y in u z)
                                                                   \in ((□(A -> B)) -> (♢A) -> ♢B).
Proof.
  repeat econstructor.
Qed.

(* λx: A ⊃ B. λy:♢A. let box u = x in dia (let dia z = y in u z)
   : (A ⊃ B) ⊃(♢A ⊃ ♢B) *)
Example Modal_Axiom_8' : forall A B,
    ~ (empty;; empty |- \x : A -> B, \y : ♢A, dia (undia z := y in x z) \in (((A -> B)) -> (♢A) -> ♢B)).
Proof.
  unfold not; intros.
  repeat match goal with
           H : _ ;; _ |- _ \in _ |- _ => inversion H; subst; clear H
         | H : has_local_type _ _ _  _ |- _ => inversion H; subst; clear H
         end.
    compute in H3; discriminate.
Qed.

Example quote_is_typed (A : ty) :
  let t := quote A in
  empty;; empty |- t \in ((□A) -> (□□A)).
Proof.
  repeat econstructor.
Qed.

Example apply_is_typed (A B : ty) :
  let t := apply A B in
  empty;; empty |- t \in ((□A -> B) -> (□A) -> □B).
Proof.
  repeat econstructor.
Qed.

Hint Constructors has_type.

Lemma canonical_forms_bool : forall t,
  empty;; empty |- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto; inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
    empty;; empty |- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal; inversion HT; subst; eauto.
Qed.

Lemma canonical_forms_box : forall t T,
  empty;; empty |- t \in (□ T) ->
  value t ->
  exists u, t = <{box u}>.
Proof.
  intros t T HT HVal.
  destruct HVal; auto; inversion HT; subst; eauto.
Qed.

Lemma canonical_forms_diamond : forall t T,
  empty;; empty |- t \in (♢ T) ->
  value t ->
  exists u, t = <{dia u}>.
Proof.
  intros t T HT HVal.
  destruct HVal; auto; inversion HT; subst; eauto.
Qed.

Theorem progress : forall t T,
  empty;; empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  rewrite HeqGamma in Ht at 1.
  remember empty as Delta.
  rewrite HeqDelta in HeqGamma.
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

Lemma inclusion_trans :
  forall Gamma Gamma' Gamma'' : context,
    inclusion Gamma Gamma' ->
    inclusion Gamma' Gamma'' ->
    inclusion Gamma Gamma''.
Proof.
  unfold inclusion; intros; eauto.
Qed.

Lemma inclusion_refl :
  forall Gamma : context,
    inclusion Gamma Gamma.
Proof.
  unfold inclusion; intros; eauto.
Qed.

Lemma weakening : forall Delta Delta' Gamma Gamma' t T,
    inclusion Delta Delta' ->
    inclusion Gamma Gamma' ->
    Delta;; Gamma  |- t \in T  -> Delta';; Gamma' |- t \in T.
Proof.
  intros Delta Delta' Gamma Gamma' t T HIncD HIncG Ht;
    revert Delta' Gamma' HIncD HIncG.
  pattern Delta, Gamma, t, T, Ht;
    eapply has_type_ind' with
    (P := fun Delta Gamma t T _ => forall Delta' Gamma' : context,
              inclusion Delta Delta' ->
              inclusion Gamma Gamma' ->
              Delta';; Gamma' |- t \in T)
    (P0 := fun Delta Gamma t T _ => forall Delta' Gamma' : context,
               inclusion Delta Delta' ->
               inclusion Gamma Gamma' ->
               has_local_type Delta' Gamma' t T); eauto using inclusion_update; clear; intros.
  - econstructor.
    eapply H; eauto; compute; eauto.
  - econstructor; eauto.
    eapply H0; eauto using inclusion_update, inclusion_refl.
  - econstructor; eauto using inclusion_update.
  - econstructor; eauto.
Qed.

Lemma local_weakening : forall Delta Delta' Gamma Gamma' t T,
    inclusion Delta Delta' ->
    inclusion Gamma Gamma' ->
    has_local_type Delta Gamma t T  ->
    has_local_type Delta' Gamma' t T.
Proof.
  intros Delta Delta' Gamma Gamma' t T HIncD HIncG Ht;
    revert Delta' Gamma' HIncD HIncG;
    induction Ht; simpl; intros;
    econstructor; eauto using weakening, inclusion_update, inclusion_refl.
Qed.

Lemma local_substitution_preserves_typing
  : forall Delta Gamma x U t v T,
    Delta;; (x |-> U; Gamma) |- t \in T ->
  empty;; empty |- v \in U   ->
  Delta;; Gamma |- [x:=v]t \in T.
Proof.
  intros Delta Gamma x U t v T Ht.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  revert x U.
  pattern Delta, Gamma', t, T, Ht;
    eapply has_type_ind' with
    (P := fun Delta Gamma' t T _ =>
            forall x U
              (Gamma : context)
              (Heq : Gamma' = (x |-> U; Gamma))
              (Hv : empty;; empty |- v \in U),
              Delta;; Gamma |- [x := v] t \in T)
    (P0 := fun Delta Gamma' t T _ =>
             forall x U
               (Gamma : context)
               (Heq : Gamma' = (x |-> U; Gamma))
               (Hv : empty;; empty |- v \in U),
               has_local_type Delta Gamma (<{[x := v] t}>) T);
    eauto using inclusion_update; clear; intros; subst; simpl; eauto.
  - (* var1 *)
    rename x0 into y.
    rename x1 into x.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite update_eq in e.
      injection e as H2; subst.
      rewrite eqb_refl; intros; eapply weakening; try eassumption;
        unfold inclusion; eauto;
        compute; congruence.
    + (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      intros; apply T_Local_Var.
      rewrite update_neq in e; auto.
  - (* abs *)
    rename x1 into x.
    rename x0 into y.
    destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl; rewrite update_shadow in h; eauto.
    +  (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      apply T_Abs.
      eapply H; eauto.
      rewrite update_permute; auto.
  - (* undia *)
    econstructor; eauto.
  - rename x0 into y.
    eapply LT_Unbox.
    + eapply H; eauto.
    + eapply H0; eauto.
  - econstructor; eauto.
Qed.

Theorem local_substitution_preserves_local_typing
  : forall Delta Gamma x U t v T,
    has_local_type Delta (x |-> U; Gamma) t T ->
    empty;; empty |- v \in U   ->
  has_local_type Delta Gamma <{[x:=v]t}> T.
Proof.
  intros Delta Gamma x U t v T Ht.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros; subst; simpl; eauto.
  - econstructor; eauto.
    eapply local_substitution_preserves_typing;
      try eassumption; try reflexivity; discriminate.
  - econstructor; eauto using local_substitution_preserves_typing;
        try eassumption; try reflexivity; try discriminate.
  - econstructor; eauto using local_substitution_preserves_typing.
Qed.

Lemma global_substitution_preserves_typing : forall Delta Gamma x U t v T,
  (x |-> U; Delta);; Gamma |- t \in T ->
  empty;; empty |- v \in U   ->
  Delta;; Gamma |- [[x:=v]]t \in T.
Proof.
  intros Delta Gamma x U t v T Ht.
  remember (x |-> U; Delta) as Delta'.
  generalize dependent Delta.
  pattern Delta', Gamma, t, T, Ht;
    eapply has_type_ind' with
    (P := fun Delta' Gamma t T _ =>
            forall
              (Delta : context)
              (Heq : Delta' = (x |-> U; Delta))
              (Hv : empty;; empty |- v \in U),
              Delta;; Gamma |- [[x := v]] t \in T)
    (P0 := fun Delta' Gamma t T _ =>
             forall
               (HId : has_local_type Delta' Gamma t T)
               (Delta : context)
               (Heq : Delta' = (x |-> U; Delta))
               (Hv : empty;; empty |- v \in U),
               has_local_type Delta Gamma (<{[[x := v]] t}>) T);
    eauto using inclusion_update; clear; intros; subst; simpl; eauto.
  - (* global_var *)
    rename u0 into u. destruct (eqb_stringP x u); subst.
    + (* x=y *)
      rewrite update_eq in e.
      injection e as H2; subst.
      rewrite eqb_refl; intros; eapply weakening; try eassumption;
        unfold inclusion; eauto;
        compute; discriminate.
    + (* x<>y *)
      rewrite (proj2 (eqb_neq x u)); eauto.
      intros; apply T_Global_Var. rewrite update_neq in e; auto.
  - (* unbox *)
    rename x0 into y. destruct (eqb_stringP x y); subst.
    + (* x=y *)
      rewrite eqb_refl.
      rewrite update_shadow in h0.
      econstructor; eauto.
    + (* x<>y *)
      rewrite (proj2 (eqb_neq x y)); eauto.
      econstructor; eauto.
      eapply H0; eauto.
      rewrite update_permute; eauto.
  - rename x0 into y.
    eapply LT_Undia.
    + apply H; eauto.
    + eapply H0; eauto.
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

Theorem global_substitution_preserves_local_typing
  : forall Delta Gamma x U t v T,
    has_local_type (x |-> U; Delta) Gamma t T ->
  empty;; empty |- v \in U   ->
  has_local_type Delta Gamma <{[[x:=v]]t}> T.
Proof.
  intros Delta Gamma x U t v T Ht.
  remember (x |-> U; Delta) as Delta'.
  generalize dependent Delta.
  induction Ht; intros; subst; simpl; eauto.
  - econstructor; eauto using global_substitution_preserves_typing.
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

Lemma delaying_preserves_local_typing
  : forall x U t v T,
    has_local_type empty (x |-> U) t T ->
    has_local_type empty empty v U   ->
    has_local_type empty empty <{〈 x := v〉t}> T.
Proof.
  intros x U t v T Ht Hv.
  remember empty as Gamma.
  rewrite HeqGamma in Hv at 1, Ht at 1.
  rewrite HeqGamma at 1.
  remember empty as Delta.
  rewrite HeqDelta in HeqGamma.
  generalize dependent T.
  revert HeqDelta HeqGamma.
  pattern Delta, Gamma, v, U, Hv.
    eapply has_local_type_ind' with
      (P := (fun Delta Gamma v U _ =>
               forall
                 (HeqDelta : Delta = empty)
                 (HeqGamma : Gamma = empty) (T : ty),
                 has_local_type Delta (x |-> U; Gamma) t T ->
                 has_local_type Delta Gamma <{ 〈 x := v〉  t }> T))
      (P0 := (fun Delta Gamma v U _ =>
                forall
                 (HeqDelta : Delta = empty)
                 (HeqGamma : Gamma = empty) (T : ty),
                 has_local_type Delta (x |-> U; Gamma) t T ->
                 has_local_type Delta Gamma <{ 〈 x := v〉  t }> T));
      simpl; intros;
      try solve [subst;
                 eauto using local_substitution_preserves_local_typing].
  - admit.
    (* simpl; econstructor; eauto.
    eapply H0; eauto using inclusion_update.
    + unfold update, t_update; simpl.
      destruct (eqb_stringP x0 x); subst; eauto.
      destruct H2; eauto.
    + unfold not; intros.
      eapply H4; eauto. *)
  - admit.
    (* simpl; econstructor; eauto.
    eapply H0; eauto using inclusion_update.
    + unfold update, t_update; simpl.
      destruct (eqb_stringP x0 x); subst; eauto.
      destruct H2; eauto.
      unfold global_context; rewrite H3; reflexivity.
    + unfold not; intros.
      eapply H4; eauto. *)
  - simpl; econstructor; eauto.
    admit.
Admitted.

(* Alas, it appears that we cannot escape variable renaming :p *)

Theorem preservation : forall t t' T,
  empty;; empty |- t \in T  ->
  t --> t'  ->
  empty;; empty |- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  rewrite HeqGamma in HT at 1.
  remember empty as Delta.
  rewrite HeqDelta in HeqGamma.
  setoid_rewrite HeqGamma at 1.
  rewrite <- HeqDelta.
  eapply has_type_ind' with
    (P := fun Delta Gamma t T _ =>
            Delta = empty ->
            Gamma = empty ->
            forall (t' : tm) (HE : t --> t'), Delta;; Gamma |- t' \in T)
    (P0 := fun Delta Gamma t T _ =>
             Delta = empty ->
             Gamma = empty ->
             forall (t' : tm) (HE : t --> t'), has_local_type Delta Gamma t' T)
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
  - inversion HE; subst...
    + econstructor; eauto.
    + eapply global_substitution_preserves_local_typing; eauto.
      inversion h; subst; assumption.
  - econstructor; eauto.
Qed.
