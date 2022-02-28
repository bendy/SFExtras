From PLF Require Import Imp.
From PLF Require Import Maps.
From DS Require Import Fixpoints.
From Coq Require Import Lia.

Definition AExpDom := PSet (nat * state).
Definition BExpDom := PSet (bool * state).
Definition ComDom := PSet (state * state).

Reserved Notation "'[[' a ']]A'" (at level 40).
Reserved Notation "'[[' b ']]B'" (at level 40).
Reserved Notation "'[[' c ']]'" (at level 40).

Declare Scope denote_scope.

Notation "{{ v | P }}" := (fun v => P)
                                (v pattern)
                              : denote_scope.


Open Scope denote_scope.

(* The semantic domain for arithmetic expressions is pairs of states
   and numbers: *)

(* ⟦n⟧A ≡ {(σ, n)}
   ⟦x⟧A ≡ {(σ, σ(x))}
   ⟦a1+a2⟧A ≡ {(σ, n + m) | (σ, n) ∈ ⟦a1⟧A ∧ (σ, m) ∈ ⟦a2⟧A}
   ⟦a1-a2⟧A ≡ {(σ, n - m) | (σ, n) ∈ ⟦a1⟧A  ∧ (σ, m) ∈ ⟦a2⟧A}
   ⟦a1*a2⟧A ≡ {(σ, n * m) | (σ, n) ∈ ⟦a1⟧A  ∧ (σ, m) ∈ ⟦a2⟧A} *)
Fixpoint denote_A (a : aexp) : AExpDom :=
  match a with
  | ANum n => {{ ( m, st ) | m = n }}

  | AId x  => {{ ( m, st ) |  m = st x }}

  | <{a1 + a2}> => {{ (n', st) |
                      exists v1 v2,
                      (v1, st) ∈ [[ a1 ]]A
                      /\ (v2, st) ∈ [[ a2 ]]A
                      /\ n' = v1 + v2 }}

  | <{a1 - a2}> => {{ (n', st) |
                      exists v1 v2,
                      (v1, st) ∈ [[ a1 ]]A
                      /\ (v2, st) ∈ [[ a2 ]]A
                      /\ n' = v1 - v2 }}

  | <{a1 * a2}> => {{ (n', st) |
                      exists v1 v2,
                      (v1, st) ∈ [[ a1 ]]A
                      /\ (v2, st) ∈ [[ a2 ]]A
                      /\ n' = v1 * v2 }}
  end
where "'[[' a ']]A'" := (denote_A a).

(* The semantic domain for boolean expressions is pairs of states
   and numbers:

   ⟦true⟧B ≡ {(σ, true)}
   ⟦false⟧B ≡ {(σ, false)}
   ⟦a1 == a2⟧B ≡ {(σ, n =? m) | (σ, n) ∈ ⟦a1⟧B ∧ (σ, m) ∈ ⟦a2⟧B}
   ⟦a1 <= a2⟧B ≡ {(σ, n <=? m) | (σ, n) ∈ ⟦a1⟧B  ∧ (σ, m) ∈ ⟦a2⟧B}
   ⟦b1 && b2⟧B ≡ {(σ, v1 && v2) | (σ, v1) ∈ ⟦b1⟧B  ∧ (σ, v2) ∈ ⟦b2⟧B} *)
Fixpoint denote_B (b : bexp) : BExpDom :=
  match b with
  | <{true}> => {{ (v, st) | v = true }}

  | <{false}> => {{ (v, st) | v = false }}

  | <{a1 = a2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 = v2 <-> v = true)}}

  | <{a1 <> a2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 = v2 <-> v = false) }}

  | <{ a1 <= a2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 <= v2 <-> v = true) }}

  | <{ a1 > a2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 > v2 <-> v = true) }}

  | <{~ b1}> => {{ (v, st) |  (negb v, st) ∈ [[ b1 ]]B }}

  | <{b1 && b2}> => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ b1 ]]B /\ (v2, st) ∈ [[ b2 ]]B
    /\ v = (andb v1 v2) }}
  end
where "'[[' b ']]B'" := (denote_B b).

(* Two expressions are semantically equivalent if their denotation is
   the same set of states and values. *)
Definition aexp_eqv (a a' : aexp) : Prop :=
  Same_set ([[ a ]]A) ([[ a' ]]A).

Definition bexp_eqv (b b' : bexp) : Prop :=
  Same_set ([[ b ]]B) ([[ b' ]]B).

Notation "a1 '==A' a2 " := (aexp_eqv a1 a2) (at level 40).
Notation "b1 '==B' b2 " := (bexp_eqv b1 b2) (at level 40).

(* Since expression equivalence is defined in terms of set
   equivalence, we can obtain proofs that it is reflexive,
   transititve, and symmetric for 'free'. *)

Lemma aexp_eqv_refl : forall (a : aexp),
    a ==A a.
Proof. intro; apply Same_set_refl. Qed.

Lemma aexp_eqv_sym : forall (a1 a2 : aexp),
    a1 ==A a2 -> a2 ==A a1.
Proof. intros; apply Same_set_sym; assumption. Qed.

Lemma aexp_eqv_trans : forall (a1 a2 a3 : aexp),
    a1 ==A a2 -> a2 ==A a3 -> a1 ==A a3.
Proof. intros; eapply Same_set_trans; eassumption. Qed.

Lemma bexp_eqv_refl : forall (b : bexp),
    b ==B b.
Proof. intro; apply Same_set_refl. Qed.

Lemma bexp_eqv_sym : forall (b1 b2 : bexp),
    b1 ==B b2 -> b2 ==B b1.
Proof. intros; apply Same_set_sym; assumption. Qed.

Lemma bexp_eqv_trans : forall (b1 b2 b3 : bexp),
    b1 ==B b2 -> b2 ==B b3 -> b1 ==B b3.
Proof. intros; eapply Same_set_trans; eassumption. Qed.

(* We can reason about equivalence of two expressions by reasoning
   about their denotations, allowing us to use any lemmas or theorems
   about sets. *)

Theorem axp_eqv_example: <{ X + Y }> ==A <{ Y + X }>.
Proof.
  (* To show two expressions are equivalent, we need to prove their
  denotations are the same. That is, we need to show that every
  element in the denotation of [X + Y] is included in [Y + X] and vice
  versa. *)
  split; intros (n, st) In_st.
  - (* In the first case, we need to show that
       (n, st) ∈ [[X + Y]]A implies  (n, st) ∈ [[Y + X]]A *)
  (* [In_inversion] is a custom tactic for working with assumptions
     about memembership in a set. It is defined in Fixpoints.v *)
    simpl in In_st. In_inversion. subst.
    (* [In_intro] is a custom tactic for working with goals about set
       memembership, it is also defined in Fixpoints.v *)
    simpl. In_intro.
    exists (st Y), (st X); repeat split. lia.
  - (* In the second case, we need to show that
       (n, st) ∈ [[Y + X]]A implies  (n, st) ∈ [[X + Y]]A *)
    simpl in In_st. In_inversion.
    In_intro.
    eexists (st X), (st Y); repeat split.
    lia.
Qed.

Theorem axp_eqv_example_2: <{ X - X }> ==A <{ 0 }>.
Proof.
  split; simpl; intros (n, st) In_st.
  - In_inversion. subst.
    In_intro; lia.
  - In_inversion.
    In_intro.
    eexists (st X), (st X); repeat split.
    lia.
Qed.

(* The semantics of boolean expressions is /compositional/: the
   meaning of an expression is derived from meaning of its
   subexpressions. We can exploit this property to show that
   expression equivalence is a /congruence/: that two expressions are
   equivalent if their subexpressions are equivalent.  *)
Lemma beq_eqv_cong : forall a1 a2 a1' a2',
    a1 ==A a1' ->
    a2 ==A a2' ->
    <{a1 = a2}> ==B <{a1' = a2'}>.
Proof.
  intros a1 a2 a1' a2' a1_eqv a2_eqv; split;
    intros (b, st) v_In.
  - (* Since [[a1 = a2]]B and [[a1' = a2']]B are built from the
       results of [[a1]]A, [[a2]]A, [[a1']]A, and [[a2]]A, their
       equivalence follows from the assumptions that [[a1]]A and
       [[a2]]A are equivalent to [[a1']]A [[a2']]A *)
    simpl in *; In_inversion; In_intro.
    exists x, x0.
    repeat split; try tauto.
    + apply a1_eqv; assumption.
    + apply a2_eqv; assumption.
  - simpl in *; In_inversion; In_intro.
    exists x, x0.
    repeat split; try tauto.
    + apply a1_eqv; assumption.
    + apply a2_eqv; assumption.
Qed.

Lemma ble_eqv_cong : forall a1 a2 a1' a2',
    a1 ==A a1' ->
    a2 ==A a2' ->
    <{a1 <= a2}> ==B <{a1' <= a2'}>.
Proof.
  intros a1 a2 a1' a2' a1_eqv a2_eqv; split;
    simpl; intros (b, st) v_In; In_inversion.
  - In_intro.
    exists x, x0.
    repeat split; try tauto.
    + apply a1_eqv; assumption.
    + apply a2_eqv; assumption.
  - In_intro.
    exists x, x0.
    repeat split; try tauto.
    + apply a1_eqv; assumption.
    + apply a2_eqv; assumption.
Qed.

Lemma bnot_eqv_cong : forall b1 b1',
    b1 ==B b1' ->
    <{~ b1}> ==B <{~ b1'}>.
Proof.
  intros b1 b1' b1_eqv; split;
    simpl; intros (b, st) v_In; In_inversion.
  - In_intro. apply b1_eqv; assumption.
  - In_intro. apply b1_eqv; assumption.
Qed.

Lemma band_eqv_cong : forall b1 b2 b1' b2',
    b1 ==B b1' ->
    b2 ==B b2' ->
    <{b1 && b2}> ==B <{b1' && b2'}>.
Proof.
  intros b1 b2 b1' b2' b1_eqv b2_eqv; split;
    simpl; intros (b, st) v_In; In_inversion.
  - In_intro.
    exists x, x0; repeat split; try assumption.
    apply b1_eqv; assumption.
    apply b2_eqv; assumption.
  - In_intro.
    exists x, x0; repeat split; try assumption.
    apply b1_eqv; assumption.
    apply b2_eqv; assumption.
Qed.

(* These congruence facts are quite useful for reasonin about
   particular expressions. *)
Theorem bexp_eqv_example: <{ X - X = 0 }> ==B <{ true }>.
Proof.
  (* We first use the fact that equivalence (i.e. set equality) is
  transitive to simplify the left-hand side of the equality. *)
  eapply bexp_eqv_trans with (b2 := <{0 = 0}>).
  - apply beq_eqv_cong.
    + apply axp_eqv_example_2.
    + eapply aexp_eqv_refl.
  - split; simpl; intros (b, st) v_In; In_inversion; In_intro; subst.
    + apply H1; reflexivity.
    + exists 0, 0; repeat split.
Qed.

(* The semantic domain for commands is pairs of initial and final
   states: *)

(*⟦skip⟧C ≡ {(σ, σ)}
  ⟦x:=a⟧C ≡ {(σ, [x↦v]σ) | (σ, v) ∈ ⟦a⟧A }
  ⟦c1;c2⟧C ≡ {(σ1, σ3) | ∃σ2.    (σ1, σ2) ∈ ⟦c1⟧c
                                     ⋀ (σ2, σ3) ∈ ⟦c2⟧c}
  ⟦if b then ct else ce⟧C ≡
     {(σ1, σ2) | (σ1, true) ∈ ⟦eB⟧B ⋀ (σ1, σ2) ∈ ⟦ct⟧C }
   ∪ {(σ1, σ2) | (σ1, false) ∈ ⟦eB⟧B ⋀ (σ1, σ2) ∈ ⟦ce⟧C}

  ⟦while b do c end⟧C ≡ LFP F

  where
  F(rec) = {(σ, σ) | (σ, false) ∈ ⟦b⟧B}
           ∪ {(σ1, σ3) | (σ1, true) ∈ ⟦b⟧B
                              ∧ ∃σ2. (σ1, σ2) ∈ ⟦c⟧c
                                      ⋀ (σ2, σ3) ∈ rec} *)

(*The denotation of while loops uses the least fixed point [LFP]
  combinator defined in Fixpoints.v. *)
Fixpoint denote_Com (c : com)
  : ComDom :=
  match c with
  | <{ skip }> =>
    {{ (st, st') | st = st' }}
  | <{x := a1}> => {{ (st, st') | exists v,
                               (v, st) ∈ [[a1]]A
                               /\ st' = t_update st x v }}

  | <{c1; c2}> => {{ (st, st') |
                   exists st'',
                   (st, st'') ∈ [[c1]] /\
                   (st'', st') ∈ [[c2]] }}

  | <{ if b then c1 else c2 end }> =>
    {{ (st, st') |
      ((true, st) ∈ [[b]]B /\ (st, st') ∈ [[c1]])
      \/ ((false, st) ∈ [[b]]B /\ (st, st') ∈ [[c2]]) }}

  | <{ while b do c end }> =>
    LFP (fun (phi : PSet _) =>
           {{ (st, st') |
              ((false, st) ∈ [[b]]B /\ st' = st)
               \/ (exists st'',
                      (true, st) ∈ [[b]]B /\
                      (st, st'') ∈ [[c]]
                      /\  (st'', st') ∈ phi) }})


  end
where "'[[' c ']]'" := (denote_Com c).

(* Two commands are semantically equivalent if their denotation is the
   same set of starting and final states. *)

Definition com_eqv (c c' : com) : Prop :=
  Same_set ([[ c ]]) ([[c']]).

Notation "c1 '==C' c2 " := (com_eqv c1 c2) (at level 40).

(* Using the denotational semantics of commands, we can prove that
   programs have the same meaning: *)
Lemma seq_skip_opt :
  forall c,
    <{skip; c}> ==C c.
Proof.
  intros c; split; intros (st, st') In_st.
  - (* (st, st') ∈ [[skip; c]] -> (st, st') ∈ [[c]] *)
    simpl in *; In_inversion.
    subst.
    In_intro; assumption.
  - (* (st, st') ∈ [[c]] -> (st, st') ∈ [[skip; c]] *)
    (* In this case, we need to show that (st, st') ∈ [[skip; c]] by
       giving an intermediate state [st''], such that (st, st'') ∈
       [[skip]] and (st'', st') ∈ [[c]]. Since [[skip]] only contains
       pairs of the same state, the state [st] fits the bill.  *)
    simpl in *. In_intro.
    exists st; split.
    + reflexivity.
    + assumption.
Qed.

(* Using the denotational semantics of commands, we can show that if
   the condition of an if expression is equivalent to true, the entire
   expression is semantically equivalent to the then branch: *)

Theorem if_true: forall b c1 c2,
    b ==B <{true}>  ->
    <{ if b then c1 else c2 end }> ==C  c1.
Proof.
  intros b c1 c2 Hb.
  split; intros (st, st') st_In.
  - (* We need to show that (st, st') ∈ [[<{ if b then c1 else c2 end }>]]
       implies (st, st') ∈ [[c1]] *)
    (* By simplifying [[<{ if b then c1 else c2 end }>]], we can do
       case analysis on what must be true of (st, st') if it is a
       member of that set. *)
    simpl in st_In; In_inversion.
    + (* In particular, either ([[b ]]B) ∈ (true, st) or ([[b ]]B) ∈ (false, st). *)
      (* The first case follows trivially. *)
      assumption.
    + (* In the second case, [[b ]]B ∈ (false, st) contradicts our assumption that
         [[b]]B ⊆ [[<{ true }>]]B  *)
      destruct Hb.
      simpl in H1.
      apply H1 in H.
      In_inversion.
  - (* In the other direction, We need to show that (st, st') ∈ [[c1]] implies
       (st, st') ∈ [[<{ if b then c1 else c2 end }>]].

      Here, it suffices to show that
      (st, st') ∈ {{(st0, st'0) | (true, st0) ∈ [[b ]]B /\ (st0, st'0) ∈ [[c1]]}},
      which follows immediately from the assumption that (st, st') ∈ [[c1]] and
      [[<{ true }>]]B ⊆ [[b]]B.*)
    simpl. left; split.
    + destruct Hb as [b_sub_tre true_sub_b].
      apply true_sub_b. simpl. In_intro.
    + apply st_In.
Qed.

(* To show that LFP is a proper fixed point in subsequent proofs, we
   need to show that if is applied to a monotone function. *)
Lemma while_body_monotone :
  forall b c,
    Monotone (fun (phi : PSet _) =>
           {{ (st, st') |
              ((false, st) ∈ [[b]]B /\ st' = st)
               \/ (exists st'',
                      (true, st) ∈ [[b]]B /\
                      (st, st'') ∈ [[c]]
                      /\  (st'', st') ∈ phi) }}).
Proof.
  unfold Monotone, Subset; intros.
  In_inversion.
  - In_intro. subst; left; split; try assumption; reflexivity.
  - right; eexists _; intuition; try eassumption.
    apply H; eassumption.
Qed.

Lemma If_while_eq :
  forall b c,
    <{while b do c end}> ==C <{if b then (c; while b do c end) else skip end }>.
Proof.
  unfold com_eqv; intros.
  eapply Same_set_trans.
  simpl; apply LFP_unfold.
  apply while_body_monotone.
  simpl.
  split; intros x In_x.
  - In_inversion.
    (* The denotation of [if] is built from the denotations of each branch *)
    + right. intuition. subst.
      reflexivity.
    + left. intuition.
      eexists; intuition; eassumption.
  - In_inversion.
    + right. eexists. intuition. eassumption.
      apply H1.
    + left. intuition.
Qed.

(* We can show that command equivalence is a /congruence/: that two
   programs are equivalent if their subterms are equivalent.

   The first step is to show this holds for individual commands. *)
Lemma seq_eq_cong : forall c1 c2 c1' c2',
    c1 ==C c1' ->
    c2 ==C c2' ->
    <{c1; c2}> ==C <{c1'; c2'}>.
Proof.
  intros; split; simpl; intros (st, st') X_In; In_inversion.
  - exists x; split.
    + apply H; assumption.
    + apply H0; assumption.
  - exists x; split.
    + apply H; assumption.
    + apply H0; assumption.
Qed.

Lemma if_eq_cong : forall b c1 c2 c1' c2',
    c1 ==C c1' ->
    c2 ==C c2' ->
    <{if b then c1 else c2 end}> ==C <{if b then c1' else c2' end}>.
Proof.
  intros; split; simpl; intros x X_In; In_inversion.
  - left; intuition. apply H. assumption.
  - right; intuition. apply H0. assumption.
  - left; intuition. apply H. assumption.
  - right; intuition. apply H0. assumption.
Qed.

Lemma while_eq_cong : forall b c1 c1',
    c1 ==C c1' ->
    <{while b do c1 end}> ==C <{while b do c1' end}>.
Proof.
  intros; split; simpl; intros x X_In; In_inversion.
  - intuition.
    + eapply Ind in X_In.
      apply X_In.
      unfold FClosed.
      intros ? ?.
      In_inversion.
      intuition; subst.
      * apply LFP_fold.
        apply while_body_monotone.
        left; intuition.
      * apply LFP_fold.
        apply while_body_monotone.
        right. exists x; intuition.
        apply H; assumption.
  - intuition.
    + eapply Ind in X_In.
      apply X_In.
      unfold FClosed.
      intros ? ?.
      In_inversion.
      intuition; subst.
      * apply LFP_fold.
        apply while_body_monotone.
        left; intuition.
      * apply LFP_fold.
        apply while_body_monotone.
        right.
        exists x; intuition.
        apply H; assumption.
Qed.

(* We can encode the idea of 'is a subterm' using contexts-- these are
   programs with a single hole representing where a command can be
   plugged in:*)
Inductive context : Set :=
    CHole : context
  | CSeqL : context -> com -> context
  | CSeqR : com -> context -> context
  | CIf_T : bexp -> context -> com -> context
  | CIf_E : bexp -> com -> context -> context
  | CWhile : bexp -> context -> context.

(* We can define what it means to plug in a hole by defining an
   inductive proposition. *)
Inductive Plug : com -> context -> com -> Prop :=
| plug_hole : forall c, Plug c CHole c
| plug_seq_L : forall c ctx c1 c2,
    Plug c ctx c1 ->
    Plug c (CSeqL ctx c2) <{c1; c2}>
| plug_seq_R : forall c ctx c1 c2,
    Plug c ctx c2 ->
    Plug c (CSeqR c1 ctx) <{c1; c2}>
| plug_if_then : forall c b ctx c1 c2,
    Plug c ctx c1 ->
    Plug c (CIf_T b ctx c2) <{if b then c1 else c2 end}>
| plug_if_else : forall c b ctx c1 c2,
    Plug c ctx c2 ->
    Plug c (CIf_E b c1 ctx) <{if b then c1 else c2 end}>
| plug_while_body : forall c b ctx cb,
    Plug c ctx cb ->
    Plug c (CWhile b ctx) <{while b do cb end}>.

(* We can now show that, program equivalence entails /contextual
   equivalence/-- that is, plugging them into the same program context
   results in equivalent programs. *)
Lemma contextual_equivalence :
  forall c1 c2 ctx c1' c2',
    Plug c1 ctx c1' ->
    Plug c2 ctx c2' ->
    c1 ==C c2 ->
    c1' ==C c2'.
Proof.
  induction ctx; intros; inversion H; inversion H0; subst.
  - intuition.
  - eapply seq_eq_cong.
    apply IHctx; assumption.
    apply Same_set_refl.
  - eapply seq_eq_cong.
    apply Same_set_refl.
    apply IHctx; assumption.
  - apply if_eq_cong.
    apply IHctx; assumption.
    apply Same_set_refl.
  - apply if_eq_cong.
    apply Same_set_refl.
    apply IHctx; assumption.
  - apply while_eq_cong.
    apply IHctx; assumption.
Qed.

(* Finally, we can show that the denotational and big-step operational
   semantics of Imp are equivalent:

   - Our big-step operational semantics is /sound/ with respect to the
     denotational semantics-- if a command or expression only evaluate
     to elements of their denotation. *)
Lemma Denotational_A_BigStep_Sound :
  forall a st,
    (aeval st a, st) ∈ [[a]]A.
Proof.
  intros;
  induction a; simpl; try solve [constructor]; unfold In;
  eexists _, _; repeat split; try eassumption.
Qed.

Lemma Denotational_B_BigStep_Sound :
  forall b st,
    (beval st b, st) ∈ [[b]]B.
Proof.
  induction b; simpl; intros; try solve [constructor]; unfold In.
  - eexists (aeval st a1), (aeval st a2); intuition.
    + apply Denotational_A_BigStep_Sound.
    + apply Denotational_A_BigStep_Sound.
    + rewrite H. apply PeanoNat.Nat.eqb_refl.
    + eapply PeanoNat.Nat.eqb_eq; assumption.
  - eexists (aeval st a1), (aeval st a2); intuition.
    + apply Denotational_A_BigStep_Sound.
    + apply Denotational_A_BigStep_Sound.
    + rewrite H, PeanoNat.Nat.eqb_refl; reflexivity.
    + apply Bool.negb_false_iff in H.
      eapply PeanoNat.Nat.eqb_eq; assumption.
  - eexists (aeval st a1), (aeval st a2); intuition.
    + apply Denotational_A_BigStep_Sound.
    + apply Denotational_A_BigStep_Sound.
    + eapply Compare_dec.leb_correct; assumption.
    + eapply Compare_dec.leb_complete; assumption.
  - eexists (aeval st a1), (aeval st a2); intuition.
    + apply Denotational_A_BigStep_Sound.
    + apply Denotational_A_BigStep_Sound.
    + apply Bool.negb_true_iff.
      apply PeanoNat.Nat.leb_gt; assumption.
    + apply Bool.negb_true_iff in H.
      apply PeanoNat.Nat.leb_gt; assumption.
  - rewrite Bool.negb_involutive. apply IHb.
  - eexists _, _; intuition.
    + apply IHb1.
    + apply IHb2.
Qed.

Lemma BigStep_Denotational_Sound :
  forall c st st',
    st =[c]=> st' -> (st, st') ∈ [[c]].
Proof.
  intros.
  induction H; simpl; try solve [econstructor]; unfold In.
  - (* E_Ass *)
    eexists; split; try reflexivity.
    rewrite <- H; eapply Denotational_A_BigStep_Sound.
  - (* E_Seq *)
    eexists; split; try reflexivity; eassumption.
  - (* E_IfTrue *)
    left; subst; split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Sound.
  - (* E_IfFalse *)
    right; subst; split; try eassumption.
    rewrite <- H; eapply Denotational_B_BigStep_Sound.
  - (* E_WhileEnd *)
    apply LFP_unfold.
    apply while_body_monotone.
    left.
    intuition.
    rewrite <- H; apply Denotational_B_BigStep_Sound.
  - (* E_WhileLoop *)
    apply LFP_unfold.
    apply while_body_monotone.
    right.
    eexists; repeat split; try eassumption.
    rewrite <- H; apply Denotational_B_BigStep_Sound.
Qed.

(* Similarly, our denotational semantics is adequate with respect to
   our big-step semantics-- when executed in an initial state included
   in the denotation of an expression or command, that expression or
   command will evaluate to the corresponding final state in the
   denotation. *)

Lemma BigStep_A_Denotational_Adequate :
  forall a st v,
    (v, st) ∈ [[a]]A
    -> v = aeval st a.
Proof.
  induction a; simpl; intros st v H;
    unfold In in H; try eassumption.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst.
    apply IHa1 in denote_a1; apply IHa2 in denote_a2.
    subst; reflexivity.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst.
    apply IHa1 in denote_a1; apply IHa2 in denote_a2.
    subst; reflexivity.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst.
    apply IHa1 in denote_a1; apply IHa2 in denote_a2.
    subst; reflexivity.
Qed.

Lemma BigStep_B_Denotational_Adequate :
  forall b st v,
    (v, st) ∈ [[b]]B
    -> beval st b = v.
Proof.
  induction b; intros st v H; In_inversion.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst; simpl.
    apply BigStep_A_Denotational_Adequate in denote_a1.
    apply BigStep_A_Denotational_Adequate in denote_a2.
    subst.
    destruct (Nat.eqb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
    + rewrite H; try reflexivity.
      apply PeanoNat.Nat.eqb_eq.
      assumption.
    + apply EqNat.beq_nat_false in Heqb.
      destruct v; eauto.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst; simpl.
    apply BigStep_A_Denotational_Adequate in denote_a1.
    apply BigStep_A_Denotational_Adequate in denote_a2.
    subst.
    destruct (Nat.eqb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
    + rewrite H; try reflexivity.
      apply PeanoNat.Nat.eqb_eq.
      assumption.
    + apply EqNat.beq_nat_false in Heqb.
      destruct v; eauto; intuition.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst; simpl.
    apply BigStep_A_Denotational_Adequate in denote_a1.
    apply BigStep_A_Denotational_Adequate in denote_a2.
    subst. intuition.
    destruct (Nat.leb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
    + rewrite H; try reflexivity.
      apply Compare_dec.leb_complete; assumption.
    + apply Compare_dec.leb_complete_conv in Heqb.
      destruct v; eauto; intuition; lia.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst; simpl.
    apply BigStep_A_Denotational_Adequate in denote_a1.
    apply BigStep_A_Denotational_Adequate in denote_a2.
    subst. intuition.
    destruct (Nat.leb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
    + destruct v; eauto; intuition.
      apply Compare_dec.leb_complete in Heqb; lia.
    + destruct v; eauto; intuition.
      apply Compare_dec.leb_complete_conv in Heqb; intuition.
  - simpl in H; In_inversion.
    simpl; rewrite IHb with (v := negb v).
    + apply Bool.negb_involutive.
    + apply H.
  - simpl in *.
    destruct H as [v1 [v2 [denote_b1 [denote_b2 v_eq] ] ] ]; subst; simpl.
    erewrite IHb1, IHb2 by eassumption.
    reflexivity.
Qed.

Lemma Denotational_BigStep_Adequate :
  forall c st st',
    (st, st') ∈ [[c]] -> st =[c]=> st'.
Proof.
  induction c; unfold In; simpl; intros st st' denote_c.
  - (* skip *)
    subst; econstructor.
  - (* Assignment *)
    destruct denote_c as [v [? ?] ].
    subst; econstructor.
    erewrite BigStep_A_Denotational_Adequate; try reflexivity; assumption.
  - (* Sequence *)
    destruct denote_c as [v [denote_c1 denote_c2] ].
    subst; econstructor.
    + apply IHc1; eassumption.
    + apply IHc2; eassumption.
  - (* Conditional *)
    destruct denote_c as [ [denote_b denote_c1] | [denote_b denote_c2] ].
    + constructor.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      apply IHc1; eassumption.
    + apply E_IfFalse.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      apply IHc2; eassumption.
  - apply LFP_unfold in denote_c; try apply while_body_monotone.
    In_inversion.
    + rewrite H0; econstructor.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
    + eapply E_WhileTrue.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      apply IHc; eassumption.
      replace x with (fst (x, st')) by reflexivity.
      replace st' with (snd (x, st')) at 2 by reflexivity.
      pattern (x, st').
      (* Hmmmm... we're (almost) back to where we started! *)
      (* Why can't we apply the Inductive Hypothesis? *)
      eapply Ind; try eassumption.
      generalize IHc; clear.
      intros IHc [st'' st']
             [ [denote_b st_eq]
             | [st''0 [denote_b [denote_c ? ] ] ] ].
      * subst; econstructor.
        erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      * econstructor.
        erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
        apply IHc; eassumption.
        apply H.
Qed.

(* Finally, we can use these soundness and adequacy results to show
   that contextual equivalence holds for a notion of equivalence
   defined in terms of the operational semantics. *)
Lemma big_step_contextual_equivalence :
  forall c1 c2 ctx c1' c2',
    Plug c1 ctx c1' ->
    Plug c2 ctx c2' ->
    (forall st st', st =[c1]=> st' <-> st =[c2]=> st') ->
    (forall st st', st =[c1']=> st' <-> st =[c2']=> st').
Proof.
  split; intros.
  - apply Denotational_BigStep_Adequate.
    eapply (contextual_equivalence c1 c2 ctx c1' c2' H H0).
    + split; intros ? ?; In_inversion.
      * eapply BigStep_Denotational_Sound.
        apply H1.
        apply Denotational_BigStep_Adequate.
        assumption.
      * eapply BigStep_Denotational_Sound.
        apply H1.
        apply Denotational_BigStep_Adequate.
        assumption.
    + eapply BigStep_Denotational_Sound.
      assumption.
  - apply Denotational_BigStep_Adequate.
    eapply (contextual_equivalence c1 c2 ctx c1' c2' H H0).
    + split; intros ? ?; In_inversion.
      * eapply BigStep_Denotational_Sound.
        apply H1.
        apply Denotational_BigStep_Adequate.
        assumption.
      * eapply BigStep_Denotational_Sound.
        apply H1.
        apply Denotational_BigStep_Adequate.
        assumption.
    + eapply BigStep_Denotational_Sound.
      assumption.
Qed.
