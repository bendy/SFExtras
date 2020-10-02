From LF Require Import Imp.
From LF Require Import Maps.
From Top Require Import Fixpoints.

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

  | APlus a1 a2 => {{ (n', st) |
                      exists v1 v2,
                      (v1, st) ∈ [[ a1 ]]A
                      /\ (v2, st) ∈ [[ a2 ]]A
                      /\ n' = v1 + v2 }}

  | AMinus a1 a2 => {{ (n', st) |
                      exists v1 v2,
                      (v1, st) ∈ [[ a1 ]]A
                      /\ (v2, st) ∈ [[ a2 ]]A
                      /\ n' = v1 - v2 }}

  | AMult a1 a2 => {{ (n', st) |
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
  | BTrue => {{ (v, st) | v = true }}

  | BFalse => {{ (v, st) | v = false }}

  | BEq a1 a2 => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 = v2 -> v = true)
    /\ (v1 <> v2 -> v = false) }}

  | BLe a1 a2 => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ a1 ]]A /\ (v2, st) ∈ [[ a2 ]]A
    /\ (v1 <= v2 -> v = true)
    /\ (~ v1 <= v2 -> v = false) }}

  | BNot b1 => {{ (v, st) |  (negb v, st) ∈ [[ b1 ]]B }}

  | BAnd b1 b2 => {{ (v, st) |
    exists v1 v2,
    (v1, st) ∈ [[ b1 ]]B /\ (v2, st) ∈ [[ b2 ]]B
    /\ v = (andb v1 v2) }}
  end
where "'[[' b ']]B'" := (denote_B b).

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
Definition com_eq (c c' : com) : Prop :=
  Same_set ([[ c ]]) ([[c']]).

(* [In_inversion] is a custom tactic for working with assumptions
   about memembership in a set. It is defined in Fixpoints.v *)

(* We can use denotations to prove that programs have the same
   meaning. *)
Lemma seq_skip_opt :
  forall c,
    com_eq <{skip; c}> c.
Proof.
  unfold com_eq. unfold Same_set, Subset. simpl; split; intros.
  - In_inversion.
    destruct H as [? [? ?] ].
    In_inversion. subst.
    assumption.
  - In_inversion.
    exists x0.
    split.
    + reflexivity.
    + assumption.
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
  intuition.
  - subst; left; intuition.
  - destruct H1 as [st' [? [? ?] ] ].
    right; eexists _; intuition; try eassumption.
    apply H; eassumption.
Qed.

Lemma If_while_eq :
  forall b c,
    com_eq <{while b do c end}>
    <{if b then (c; while b do c end) else skip end }>.
Proof.
  unfold com_eq; intros.
  eapply Same_set_trans.
  simpl; apply LFP_unfold.
  apply while_body_monotone.
  simpl.
  split; intros x In_x.
  - In_inversion.
    (* The denotation of [if] is built from the denotations of each branch *)
    destruct In_x.
    + right. intuition. subst.
      reflexivity.
    + destruct H as [st' [? [? ?] ] ].
      left. intuition.
      eexists; intuition; eassumption.
  - In_inversion.
    intuition.
    + In_inversion.
      destruct H1 as [st' [? ?] ].
      right. eexists. intuition. eassumption.
      apply H1.
    + left. intuition.
Qed.

(* We can show that program equivalence is a /congruence/: that two
   programs are equivalent if their subterms are equivalent.

   The first step is to show this holds for individual commands. *)
Lemma seq_eq_cong : forall c1 c2 c1' c2',
    com_eq c1 c1' ->
    com_eq c2 c2' ->
    com_eq <{c1; c2}> <{c1'; c2'}>.
Proof.
  intros; split; simpl; intros x X_In; In_inversion.
  - destruct X_In as [st' [? ?] ].
    exists st'; split.
    + apply H; assumption.
    + apply H0; assumption.
  - destruct X_In as [st' [? ?] ].
    exists st'; split.
    + apply H; assumption.
    + apply H0; assumption.
Qed.

Lemma if_eq_cong : forall b c1 c2 c1' c2',
    com_eq c1 c1' ->
    com_eq c2 c2' ->
    com_eq <{if b then c1 else c2 end}> <{if b then c1' else c2' end}>.
Proof.
  intros; split; simpl; intros x X_In; In_inversion.
  - intuition.
    + left; intuition. apply H. assumption.
    + right; intuition. apply H0. assumption.
  - intuition.
    + left; intuition. apply H. assumption.
    + right; intuition. apply H0. assumption.
Qed.

Lemma while_eq_cong : forall b c1 c1',
    com_eq c1 c1' ->
    com_eq <{while b do c1 end}> <{while b do c1' end}>.
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
        right. destruct H1 as [st' [? [? ?] ] ].
        exists st'; intuition.
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
        right. destruct H1 as [st' [? [? ?] ] ].
        exists st'; intuition.
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
    com_eq c1 c2 ->
    com_eq c1' c2'.
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
    + apply PeanoNat.Nat.eqb_neq; assumption.
  - eexists (aeval st a1), (aeval st a2); intuition.
    + apply Denotational_A_BigStep_Sound.
    + apply Denotational_A_BigStep_Sound.
    + apply Compare_dec.leb_correct; assumption.
    + apply PeanoNat.Nat.leb_nle. assumption.
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
    + rewrite H0; try reflexivity.
      apply PeanoNat.Nat.eqb_neq in Heqb.
      assumption.
  - destruct H as [v1 [v2 [denote_a1 [denote_a2 v_eq] ] ] ]; subst; simpl.
    apply BigStep_A_Denotational_Adequate in denote_a1.
    apply BigStep_A_Denotational_Adequate in denote_a2.
    subst. intuition.
    destruct (Nat.leb (aeval st a1) (aeval st a2)) eqn: ?; intuition.
    + rewrite H; try reflexivity.
      apply Compare_dec.leb_complete; assumption.
    + rewrite H0; try reflexivity.
      apply PeanoNat.Nat.leb_nle.
      assumption.
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
    destruct denote_c as [ [denote_b st_eq]
                         | [st'' [denote_b [denote_c ? ] ] ] ].
    + rewrite st_eq; econstructor.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
    + eapply E_WhileTrue.
      erewrite BigStep_B_Denotational_Adequate; try reflexivity; assumption.
      apply IHc; eassumption.
      replace st'' with (fst (st'', st')) by reflexivity.
      replace st' with (snd (st'', st')) at 2 by reflexivity.
      pattern (st'', st').
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
