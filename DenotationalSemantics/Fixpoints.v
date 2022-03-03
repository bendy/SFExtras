Section Sets.
  (* Extensional: Explicitly spell out all the members of a set.
     I.e. The set of states in the US is "Alabama, Alaska, ...." *)
  (* Seen this style of definition before... *)
  Definition Set' (A : Type) := list A.

  (* Intensional: Characteristic 'Function' approach: every input to a
     boolean valued function which returns true is a member of the
     set, and is not an element otherwise. *)

  Definition Bool_Set (A : Type) := A -> bool.

  Fixpoint evenb (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

  Definition evens : Bool_Set nat := evenb.
  Definition In_b {A} (a : A) (e : Bool_Set A) : Prop :=
    e a = true.

  Example even_4 : In_b 4 evens. Proof. unfold In_b. simpl. reflexivity. Qed.

  Definition Same_Set' {A} (e1 e2 : Bool_Set A) : Prop :=
    forall x, e1 x = e2 x.

  (* How to define Intersection, Union, Subset ? *)
  Definition Union' {A} (e1 e2 : Bool_Set A) : Bool_Set A :=
    fun x => orb (e1 x) (e2 x).

  Definition Intersection' {A} (e1 e2 : Bool_Set A)
    : Bool_Set A :=
    fun x => andb (e1 x) (e2 x).

  Definition Subset' {A} (e1 e2 : Bool_Set A) : Prop :=
    forall x, In_b e1 x -> In_b e2 x.
  (* This encoding of sets means membership is always decideable! *)
End Sets.

Section Fixpoints.

  (* Propositional analogues to Characteristic Function from above.  A
     set is a property (propositional-valued function), and an object
     is an element if there is some proof that it satisfies that property. *)
  Definition PSet (A : Type) := A -> Prop.
  Definition In {A} (a : A) (e : PSet A) : Prop := e a.
  Notation "x '∈' e" := (In x e) (at level 60).

  Definition even x := exists n : nat, x = 2 * n.

  Example even_6 : 6 ∈ even. Proof. unfold In. exists 3. reflexivity. Qed.

  Definition Subset {A} (e1 e2 : PSet A) : Prop :=
    forall x, x ∈ e1 -> x ∈ e2.

  Notation "s1 ⊆ s2" := (Subset s1 s2) (at level 60).

  Lemma Subset_trans {A} : forall (s1 s2 s3 : PSet A),
      s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
  Proof.
    unfold Subset; intros.
    apply H0.
    apply H.
    assumption.
  Qed.

  Lemma Subset_refl {A} : forall (s1 : PSet A), s1 ⊆ s1.
  Proof.
    unfold Subset; intros.
    assumption.
  Qed.

  Definition Same_set {A} (s1 s2 : PSet A) := s1 ⊆ s2 /\ s2 ⊆ s1.

  Lemma Same_set_refl {A} : forall (s1 : PSet A), Same_set s1 s1.
  Proof.
    unfold Same_set; split.
    - apply Subset_refl.
    - apply Subset_refl.
  Qed.

  Lemma Same_set_sym {A} : forall (s1 s2 : PSet A), Same_set s1 s2 -> Same_set s2 s1.
  Proof.
    unfold Same_set; intros s1 s2 [? ?]; split; assumption.
  Qed.

  Lemma Same_set_trans {A} : forall (s1 s2 s3 : PSet A),
      Same_set s1 s2 ->
      Same_set s2 s3 ->
      Same_set s1 s3.
  Proof.
    unfold Same_set; intros s1 s2 s3 [? ?] [? ?]; split.
    - eapply Subset_trans; eassumption.
    - eapply Subset_trans; eassumption.
  Qed.

  Context {U : Type}. (* The type of elements of our set. *)
  Variable F : PSet U -> PSet U. (* Our generating function-- takes a set of Us and builds a new set.*)

  (* A generator function is monotone if it preserves the subset
  relation on its argument. *)
  Definition Monotone (F : PSet U -> PSet U) : Prop :=
    forall (S S' : PSet U),
      S ⊆ S' -> F S ⊆ F S'.

  Variable Monotone_F : Monotone F.

  Definition FClosed (S : PSet U) : Prop := F S ⊆ S.

  Definition FConsistent (S : PSet U) : Prop := S ⊆ F S.

  Definition FixedPoint (S : PSet U) : Prop :=
    FClosed S /\ FConsistent S.

  Lemma FixedPoint_unfold FP : FixedPoint FP -> Same_set FP (F FP).
  Proof.
    unfold Same_set; intros [? ?]; split.
    - apply H0.
    - apply H.
  Qed.

  (* LFP is defined as the intersection of all F-closed sets. An
     element is in LFP iff it is a member of every F-Closed set. *)
  Definition LFP : PSet U :=
    fun a => forall S, FClosed S -> a ∈ S.

  Theorem LFP_is_FClosed
    : FClosed LFP.
  Proof.
    unfold FClosed.
    (* By the definition of LFP, it is a subset of every F-Closed set. *)
    assert (forall (X : PSet U), FClosed X -> LFP ⊆ X).
    { unfold Subset; intros. apply H0.  assumption. }
    (* Since F is monotone, the previous fact entails that [F LFP ⊆ F X]
       for every F-Closed set X.*)
    assert (forall (X : PSet U), FClosed X -> F LFP ⊆ F X).
    { intros. apply Monotone_F. apply H. assumption. }
    (* By transitivity of the subset relation, it follows that [F LFP ⊆ X]
       for every F-Closed set X.  *)
    assert (forall (X : PSet U), FClosed X -> F LFP ⊆ X).
    { intros. apply Subset_trans with (s2 := F X).
      - apply H0. assumption.
      - apply H1. }
    (* Now we just need to show that every element of [F LFP] is an
       element of [LFP], By definition, this is equivalent to showing
       that every element of [F LFP] is also a member of every
       F-Closed set. This follows from the fact that [F LFP] is a
       the previously proof that [F LFP] is a subset of every F-Closed set! *)
    unfold Subset; intros ? ? S FClosed_S.
    apply H1.
    assumption.
    assumption.
  Qed.

  Theorem LFP_is_FConsistent
    : FConsistent LFP.
  Proof.
    unfold FConsistent; intros.
    (*By the previous lemma, we know that F LFP ⊆ LFP. By monotonicity of
       F, F (F LFP) ⊆ F LFP. *)
    assert (F (F LFP) ⊆ F LFP).
    { apply Monotone_F. apply LFP_is_FClosed. }
    (* By definition, this means [F LFP] is F-Closed. *)
    assert (FClosed (F LFP)) by apply H.
    (* Since [F LFP] is F-Closed, it is a superset of LFP. *)
    intros x In_x.
    apply In_x.
    assumption.
  Qed.

  Theorem LFP_is_FixedPoint
    : FixedPoint LFP.
  Proof.
    unfold FixedPoint.
    split.
    - apply LFP_is_FClosed; eauto.
    - apply LFP_is_FConsistent; eauto.
  Qed.

  Theorem LFP_is_LeastFixedPoint :
    forall FP, FixedPoint FP -> LFP ⊆ FP.
  Proof.
    unfold FixedPoint; intros FP [? ?].
    intros x In_x.
    apply In_x.
    apply H.
  Qed.

  Corollary LFP_unfold : Same_set LFP (F LFP).
  Proof. apply FixedPoint_unfold. apply LFP_is_FixedPoint. Qed.

  Corollary LFP_fold : Same_set (F LFP) LFP.
  Proof. apply Same_set_sym. apply LFP_unfold. Qed.

  (* This admits the principle of Induction-- if we can show a set is
     F-Closed, it follows that every element of LFP is in that set. *)

  Lemma Ind
    : forall (Ind : PSet U),
      FClosed Ind -> forall a, LFP a -> Ind a.
  Proof.
    unfold LFP, FClosed; intros; eapply H0; eauto.
  Qed.

  (* GFP is defined as the union of all F-consistent sets.  An
     element is in GFP iff it is a member of /some/ F-Consistent set.*)
  Definition GFP : PSet U :=
    fun a => exists S, FConsistent S /\ a ∈ S.

  Lemma GFP_is_FConsistent
    : FConsistent GFP.
  Proof.
    unfold FConsistent.
    intros ? ?.
    (* By the definition of GFP, there must be some F-consistent set, X, that contains x *)
    destruct H as [X [? ?] ].
    (* Since X is F-consistent, by definition x is a member of F X. *)
    apply H in H0.
    (* We have now established that F X ⊆ F GFP: *)
    revert x H0; fold (Subset (F X) (F GFP)).
    (* Since F is monotone, it suffices to show that X ⊆ GFP *)
    eapply Monotone_F.
    (* To show X ⊆ GFP, we just need to show that every x in X is in GFP *)
    intros ? ?.
    (* By definition, x is an element of GFP if it is a member of an
    F-consistent set. By assumption, x is in X and F is F-consistent,
    so we're done!*)
    unfold In, GFP.
    eexists X.
    eauto.
  Qed.

  Lemma GFP_is_FClosed
    : FClosed GFP.
  Proof.
    intros ? ?.
    (* By our previous lemma, we know that GFP ⊆ F GFP. By monotonicity of
       F, F GFP ⊆ F (F GFP). *)
    assert (F GFP ⊆ F (F GFP)).
    { apply Monotone_F.
      apply GFP_is_FConsistent. }
    (* By definition, this means [F GFP] is F-consistent. *)
    assert (FConsistent (F GFP)).
    { intros ? ?.
      apply H0.
      assumption. }
    (* Since F is a member of an F-consistent set, it must be a member
    of GFP.*)
    unfold In, GFP.
    exists (F GFP).
    split; assumption.
  Qed.

  Theorem GFP_is_FixedPoint
    : FixedPoint GFP.
  Proof.
    unfold FixedPoint.
    split.
    - apply GFP_is_FClosed; eauto.
    - apply GFP_is_FConsistent; eauto.
  Qed.

  Theorem GFP_is_Greatest_FixedPoint
    : forall FP, FixedPoint FP -> FP ⊆ GFP.
  Proof.
    intros ? [? ?].
    intros x In_x.
    exists FP; split; assumption.
  Qed.

  (* This admits the principle of Co-Induction-- if we can show a set is
     F-Consistent, every element of that set is also in GFP. *)

  Lemma CoInd
    : forall (Ind : PSet U),
      FConsistent Ind -> forall a, Ind a -> GFP a.
  Proof.
    unfold GFP, FConsistent; intros; eauto.
  Qed.

End Fixpoints.

(*A quick example of the principle of Induction *)
Inductive isEven : nat -> Prop :=
| isEvenZero : isEven 0
| isEvenSS : forall (n : nat), isEven n -> isEven (S (S n)).

Definition isEven_F : PSet nat -> PSet nat :=
  fun X n => (n = 0) \/ (exists n', X n' /\ n = S (S n')).

Definition isEven' := LFP isEven_F.

Theorem isEven_eqv : forall n,
    isEven n <-> isEven' n.
Proof.
  split; intro.
  - induction H.
    + unfold isEven', LFP.
      intros.
      apply H.
      unfold isEven_F, In; intuition.
    + unfold isEven', LFP.
      intros.
      apply H0.
      unfold isEven_F, In; right.
      eexists; intuition.
      unfold isEven' in IHisEven.
      apply IHisEven in H0; eauto.
  - unfold LFP in H. eapply Ind; try eassumption.
    intros ? ?; unfold In in *.
    destruct H0 as [ | [n' [? ?] ] ]; subst.
    + econstructor.
    + econstructor.
      eassumption.
Qed.

Notation "x '∈' e" := (In x e) (at level 60).
Notation "s1 ⊆ s2" := (Subset s1 s2) (at level 60).

Lemma In_pair_inv {A B} :
  forall ab (s : PSet (Datatypes.prod A B)),
    ab ∈ s -> exists a b, ab = Datatypes.pair a b /\ s (Datatypes.pair a b).
Proof.
  destruct ab; eauto.
Qed.

Ltac In_inversion :=
  repeat match goal with
           H : @In (Datatypes.prod ?A ?B) ?ab _ |- _ =>
           apply In_pair_inv in H;
           destruct H as [? [? [? H] ] ]; subst ab
         | H : @In _ _ _ |- _ => unfold In in H
         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : exists _, _ |- _ => destruct H
         | H : _ = _ |- _ => solve [discriminate]
         end.

Ltac In_intro :=
  repeat match goal with
         | |- In _ _ => unfold In
         | |- _ = _ => solve [intuition]
         end.
