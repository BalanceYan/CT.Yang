(* Notation *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : type_scope.

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.

Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.

Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.

Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'λ' x .. y ']' , '/' t ']'").

(* Logic *)
Axiom classicT : ∀ P : Prop, P + ¬ P.

Proposition classic : ∀ P : Prop, P ∨ ¬P.
Proof. intros. destruct (classicT P); auto. Qed.

Proposition NNPP : ∀ P, (¬ (¬ P) ↔ P).
Proof. intros; destruct (classic P); tauto. Qed.

Proposition inp : ∀ P Q : Prop, (P ↔ Q) → (¬ P → ¬ Q).
Proof. intros; intro. elim H0. apply H; auto. Qed.

(* Ensemble *)
Parameter Class : Type.

Parameter In : Class → Class → Prop.
Notation "a ∈ A" := (In a A)(at level 70).
Notation "a ∉ A" := (¬ (a ∈ A))(at level 70).

Parameter Classifier : ∀ P : Class → Prop, Class.
Notation "\{ P \}" := (Classifier P)(at level 0).

Axiom ExtAx : ∀ A B : Class, A = B ↔ (∀ x, x ∈ A ↔ x ∈ B).
Ltac AppE := apply ExtAx; split; intros.

Axiom ClaAx : ∀ (x : Class) (P : Class → Prop),
  x ∈ \{ P \} ↔ (P x).

Lemma ClaI : ∀ x (P : Class → Prop), P x → x ∈ \{ P \}.
Proof. intros x P HP. apply ClaAx; auto. Qed.

Lemma ClaE : ∀ x (P : Class → Prop), x ∈ \{ P \} → P x.
Proof. intros x P Hx. apply ClaAx; auto. Qed.

Definition NoEmpty A := ∃ x, x ∈ A.
Notation "⦿ A" := (NoEmpty A) (at level 45).

Definition Empty := \{ λ x, x ≠ x \}.
Notation " ∅ " := Empty.

Lemma EmptyNI : ∀ x, x ∉ ∅.
Proof.
  intros x H. apply ClaE in H. apply H; auto.
Qed.
Ltac exfalso0 := exfalso; eapply EmptyNI; eauto.

Lemma EmptyEq : ∀ x, x = ∅ ↔ ¬ (⦿ x).
Proof.
  split; intros. subst x. intro. destruct H. exfalso0.
  AppE. elim H. exists x0; auto. exfalso0.
Qed.

Lemma EmptyNE : ∀ x, x ≠ ∅ ↔ ⦿ x.
Proof.
  intros. pose proof EmptyEq. split; intros.
  - apply inp with (Q := ¬ (⦿ x)) in H0; auto.
    apply -> NNPP in H0; auto.
  - intro. apply H in H1; auto.
Qed.

Definition Singleton x : Class := \{ λ z, z = x \}.
Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Lemma SingI : ∀ x, x ∈ [x].
Proof. intros. apply ClaAx; auto. Qed.

Lemma SingE : ∀ x y, x ∈ [y] → x = y.
Proof. intros. apply ClaE in H; auto. Qed.

Definition Included A B := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊂ B" := (Included A B)(at level 70).

Lemma ReSyTrP : ∀ A B C : Class,
  (A ⊂ A) ∧ (A ⊂ B ∧ B ⊂ A → A = B) ∧ (A ⊂ B ∧ B ⊂ C → A ⊂ C).
Proof.
  intros. split; try red; auto. split; intros.
  - AppE; apply H; auto.
  - destruct H. intros x Hx. apply H in Hx. auto.
Qed.

Definition PowerSet X : Class := \{ λ A, A ⊂ X \}.
Notation " cP( X )" := (PowerSet X)(at level 9, right associativity).

Definition Union A B := \{ λ x, x ∈ A ∨ x ∈ B \}.
Notation "A ⋃ B" := (Union A B)(at level 65, right associativity).

Definition Inter A B := \{ λ x, x ∈ A ∧ x ∈ B \}.
Notation "A ∩ B" := (Inter A B)(at level 60, right associativity).

Definition Setmin A B := \{ λ x, x ∈ A ∧ x ∉ B \}.
Notation "A - B" := (Setmin A B).

Lemma IncludP : ∀ A B X, A ⊂ X → A - B ⊂ X.
Proof. intros * Ha z Hz. apply ClaE in Hz as []; auto. Qed.

Lemma IncludP1 : ∀ A B C, A ⊂ B → A - C ⊂ B - C.
Proof.
  intros * Hab z Hz. apply ClaE in Hz. apply ClaI. firstorder.
Qed.

Lemma IncludP2 : ∀ A X, A ⊂ X → X - A ⊂ X.
Proof. intros * Hsub x Hx. apply ClaE in Hx. tauto. Qed.

Lemma Idem : ∀ A, A ⋃ A = A.
Proof. intros. AppE. apply ClaE in H; tauto. apply ClaI; auto. Qed.

Lemma Idem' : ∀ A, A ∩ A = A.
Proof. intros. AppE. apply ClaE in H; tauto. apply ClaI; auto. Qed.

Lemma Commu : ∀ A B, A ⋃ B = B ⋃ A.
Proof. intros. AppE; apply ClaE in H; apply ClaI; tauto. Qed.

Lemma Commu' : ∀ A B, A ∩ B = B ∩ A.
Proof. intros. AppE; apply ClaE in H; apply ClaI; tauto. Qed.

Lemma Distribu : ∀ A B C, (A ⋃ B) ∩ C = (A ∩ C) ⋃ (B ∩ C).
Proof.
  intros. AppE; apply ClaAx.
  - do 2 (apply ClaE in H; destruct H).
    + left; apply ClaI; auto. + right; apply ClaI; auto.
  - do 2 (apply ClaE in H; destruct H); split;
    try (apply ClaI; auto); auto.
Qed.

Lemma TwDeMorgan : ∀ A B C, A - (B ∩ C) = (A - B) ⋃ (A - C).
Proof.
  intros. AppE; apply ClaE in H; apply ClaI.
  - destruct H, (classic (x ∈ C)).
    + left; apply ClaI. split; auto. intro; elim H0. apply ClaI; tauto.
    + right; apply ClaI. split; auto.
  - destruct H; apply ClaE in H as []; split; auto;
    intro; apply ClaE in H1; destruct H1; tauto.
Qed.

Lemma EmUnion : ∀ A, A ⋃ ∅ = A.
Proof.
  intros. AppE; [| apply ClaI; eauto].
  apply ClaE in H as []; eauto. exfalso0.
Qed.

Lemma EmInter : ∀ A, A ∩ ∅ = ∅.
Proof. intros. AppE. apply ClaE in H; tauto. exfalso0. Qed.

Lemma TwSetmin : ∀ A X, A ⊂ X → X - (X - A) = A.
Proof.
  intros. AppE. apply ClaE in H0 as [Hx H0].
  destruct (classic (x ∈ A)); eauto. elim H0. apply ClaI; eauto.
  apply ClaI. split; eauto. intro. apply ClaE in H1; tauto.
Qed.

Definition EleU cA := \{ λ z, ∃ y, z ∈ y ∧ y ∈ cA \}.
Notation "∪ cA" := (EleU cA)(at level 66).

Definition EleI cA := \{ λ z, ∀ y, y ∈ cA → z ∈ y \}.
Notation "⋂ cA" := (EleI cA)(at level 66).

(* De Morgan 律 *)
Definition AAr A cA := \{λ z, ∃ Ar, Ar ∈ cA /\ z = A - Ar\}.

Lemma AArP : ∀ A cA, cA ≠ ∅ → AAr A cA ≠ ∅.
Proof.
  intros. apply EmptyNE in H as [Ar H]. apply EmptyNE.
  exists (A - Ar). apply ClaI; eauto.
Qed.

Lemma DeMorganUI : ∀ A cA, cA ≠ ∅ → (A - ∪cA) = ⋂(AAr A cA).
Proof with eauto.
  intros. AppE.
  - apply ClaE in H0 as [Hx HcA]. apply ClaI. intros.
    apply ClaE in H0 as [B [Hb Heq]]. subst. apply ClaI. split...
    intro. elim HcA. apply ClaI...
  - apply EmptyNE in H as [Ar H]. apply ClaE in H0. apply ClaI.
    assert (A - Ar ∈ AAr A cA). { apply ClaI... }
    apply H0 in H1. apply ClaE in H1 as [Hx H1]. split...
    intro. apply ClaE in H2 as [B [Hb H2]].
    assert (A - B ∈ AAr A cA). { apply ClaI... }
    apply H0 in H3. apply ClaE in H3; tauto.
Qed.
