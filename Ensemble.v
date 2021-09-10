(* Notation *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : type_scope.

Notation "x ∨ y" :=
  (x \/ y) (at level 85, right associativity) : type_scope.

Notation "x ∧ y" :=
  (x /\ y) (at level 80, right associativity) : type_scope.

Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" :=
  (x <-> y) (at level 95, no associativity): type_scope.

Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'λ' x .. y ']' , '/' t ']'").

(* Logic *)
Axiom classic : ∀ P : Prop, P ∨ ¬P.

Proposition NNPP : ∀ P, (¬ (¬ P) ↔ P).
Proof. intros; destruct (classic P); tauto. Qed.

Proposition inp : ∀ P Q : Prop, (P ↔ Q) → (¬ P → ¬ Q).
Proof. intros; intro. elim H0. apply H; auto. Qed.

(* Axiom and Ensemble *)
Parameter Class : Type.

Parameter In : Class → Class → Prop.
Notation "a ∈ A" := (In a A)(at level 70).
Notation "a ∉ A" := (¬ (a ∈ A))(at level 70).

Axiom ExtAx : ∀ A B : Class, A = B ↔ (∀ x, x ∈ A ↔ x ∈ B).
Ltac AppE := apply ExtAx; split; intros.

Definition Ensemble x : Prop := ∃ y, x ∈ y.
Ltac Ens := unfold Ensemble; eauto.

Parameter Classifier : ∀ P : Class → Prop, Class.
Notation "\{ P \}" := (Classifier P)(at level 0).

Axiom ClaAx : ∀ x P, x ∈ \{ P \} ↔ Ensemble x ∧ (P x).

Fact ClaI : ∀ x (P : Class → Prop), Ensemble x → P x → x ∈ \{ P \}.
Proof. intros * Hx HP. apply ClaAx; auto. Qed.

Fact ClaE : ∀ x (P : Class → Prop), x ∈ \{ P \} → Ensemble x ∧ P x.
Proof. intros * Hx. apply ClaAx; auto. Qed.

Definition NoEmpty A := ∃ x, x ∈ A.
Notation "⦿ A" := (NoEmpty A) (at level 45).

Definition Empty := \{ λ x, x ≠ x \}.
Notation " ∅ " := Empty.

Fact EmptyNI : ∀ x, x ∉ ∅.
Proof. intros x H. apply ClaE in H. apply H; auto. Qed.
Ltac exfalso0 := exfalso; eapply EmptyNI; eauto.

Fact EmptyEq : ∀ x, x = ∅ ↔ ¬ (⦿ x).
Proof.
  split; intros. subst x. intro. destruct H. exfalso0.
  AppE. elim H. exists x0; auto. exfalso0.
Qed.

Fact EmptyNE : ∀ x, x ≠ ∅ ↔ ⦿ x.
Proof.
  intros. pose proof EmptyEq. split; intros.
  - apply inp with (Q := ¬ (⦿ x)) in H0; auto.
    apply -> NNPP in H0; auto.
  - intro. apply H in H1; auto.
Qed.

Definition μ := \{ λ x, x = x \}.

Fact μ_En : ∀ x, x ∈ μ ↔ Ensemble x.
Proof. split; intros. Ens. apply ClaI; auto. Qed.

Definition Singleton x := \{ λ z, x ∈ μ → z = x \}.
Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Fact SingI : ∀ x, Ensemble x → x ∈ [x].
Proof. intros. apply ClaI; auto. Qed.

Fact SingE : ∀ x y, Ensemble x → y ∈ [x] → y = x.
Proof.
  intros. apply ClaE in H0 as []. apply H1. apply μ_En; auto.
Qed.

Definition Included A B := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊂ B" := (Included A B)(at level 70).

Fact ReSyTrP : ∀ A B C,
  (A ⊂ A) ∧ (A ⊂ B → B ⊂ A → A = B) ∧ (A ⊂ B → B ⊂ C → A ⊂ C).
Proof.
  intros. split. intros x; auto. split; intros.
  - AppE; auto. - intros x Hx. apply H in Hx. auto.
Qed.

Axiom SubAx : ∀ x, Ensemble x →
  ∃ y, Ensemble y ∧ (∀ z, z ⊂ x → z ∈ y).

Fact SubAxI : ∀ x z, Ensemble x → z ⊂ x → Ensemble z.
Proof. intros. apply SubAx in H as [y []]. Ens. Qed.

Definition PowerSet X := \{ λ A, A ⊂ X \}.
Notation " cP( X )" := (PowerSet X)(at level 9, right associativity).

Fact PowerIE : ∀ X Y, Ensemble X → Y ∈ cP(X) ↔ Y ⊂ X.
Proof.
  intros. split; intros. apply ClaE in H0; tauto.
  apply ClaI; auto. eapply SubAxI; eauto.
Qed.

Fact PowerP : ∀ X, Ensemble X → Ensemble cP(X) ∧
  (∀ Y, Y ⊂ X ↔ Y ∈ cP(X)).
Proof.
  intros. split.
  - pose proof H as H'. apply SubAx in H as [B [Hbe Hb]].
    assert (cP(X) ⊂ B). { intros z Hz. apply PowerIE in Hz; auto. }
    clear H'. eapply SubAxI; eauto.
  - split; intros. apply PowerIE; auto. apply PowerIE in H0; auto.
Qed.

Fact SingEn : ∀ x, Ensemble x → Ensemble [x].
Proof.
  intros. assert ([x] ⊂ cP(x)).
  { intros z Hz. apply SingE in Hz; auto. subst.
    apply PowerIE; auto. intros z; auto. }
  apply PowerP in H as []; auto. eapply SubAxI; eauto.
Qed.

Definition Union A B := \{ λ x, x ∈ A ∨ x ∈ B \}.
Notation "A ⋃ B" := (Union A B)(at level 65, right associativity).

Fact UnionIE : ∀ x A B, x ∈ A ∨ x ∈ B ↔ x ∈ (A ⋃ B).
Proof.
  intros. split; intros. destruct H as []; apply ClaI; Ens.
  apply ClaE in H. tauto.
Qed.

Fact UnionNE : ∀ x A B, x ∉ A ⋃ B → x ∉ A /\ x ∉ B.
Proof. intros. split; intro; elim H; apply UnionIE; auto. Qed.

Fact Idem : ∀ A, A ⋃ A = A.
Proof.
  intros. AppE. apply UnionIE in H. tauto. apply UnionIE; auto.
Qed.

Fact Commu : ∀ A B, A ⋃ B = B ⋃ A.
Proof. intros. AppE; apply UnionIE in H; apply UnionIE; tauto. Qed.

Fact EmUnion : ∀ A, A ⋃ ∅ = A.
Proof.
  intros. AppE. apply UnionIE in H as []; auto.
  exfalso0. apply UnionIE; Ens.
Qed.

Axiom UnionAx : ∀ X Y, Ensemble X → Ensemble Y → Ensemble (X ⋃ Y).

Definition Inter A B := \{ λ x, x ∈ A ∧ x ∈ B \}.
Notation "A ∩ B" := (Inter A B)(at level 60, right associativity).

Fact InterIE : ∀ x A B, x ∈ A ∧ x ∈ B ↔ x ∈ (A ∩ B).
Proof.
  intros. split; intros. apply ClaI; auto. destruct H; Ens.
  apply ClaE in H. tauto.
Qed.

Fact Idem' : ∀ A, A ∩ A = A.
Proof.
  intros. AppE. apply InterIE in H; tauto. apply InterIE; auto.
Qed.

Fact Commu' : ∀ A B, A ∩ B = B ∩ A.
Proof. intros. AppE; apply ClaE in H; apply ClaI; tauto. Qed.

Fact EmInter : ∀ A, A ∩ ∅ = ∅.
Proof. intros. AppE. apply InterIE in H; tauto. exfalso0. Qed.

Fact Distribu : ∀ A B C, (A ⋃ B) ∩ C = (A ∩ C) ⋃ (B ∩ C).
Proof.
  intros. AppE; apply ClaI; Ens.
  - apply InterIE in H as []. apply UnionIE in H as [H|H].
    left; apply InterIE; tauto. right; apply InterIE; tauto.
  - apply UnionIE in H as []; apply InterIE in H as [];
    split; auto; apply ClaI; auto; Ens.
Qed.

Fact DistribuLI : ∀ A B C, A ∩ (B ⋃ C) = A ∩ B ⋃ A ∩ C.
Proof.
  intros. rewrite Commu', Distribu, Commu', (Commu' A C); auto.
Qed.

Fact InterEn : ∀ X Y, Ensemble X → Ensemble Y → Ensemble (X ∩ Y).
Proof.
   intros. assert (X ∩ Y ⊂ X).
   { intros z Hz. apply ClaE in Hz; tauto. }
   clear H0. eapply SubAxI; eauto.
Qed.

Definition Setmin A B := \{ λ x, x ∈ A ∧ x ∉ B \}.
Notation "A - B" := (Setmin A B).

Fact SetminIE : ∀ x A B, x ∈ A ∧ x ∉ B ↔ x ∈ (A - B).
Proof.
  intros. split; intros. apply ClaI; auto. destruct H; Ens.
  apply ClaE in H. tauto.
Qed.

Fact SetminId : ∀ X, X - X = ∅.
Proof. intro. AppE. apply SetminIE in H; tauto. exfalso0. Qed.

Fact SetminEm : ∀ X, X - ∅ = X.
Proof.
  intro. AppE. apply SetminIE in H; tauto.
  apply SetminIE. split; auto. intro. exfalso0.
Qed.

Fact IncludP : ∀ A B X, A ⊂ X → A - B ⊂ X.
Proof. intros * Ha z Hz. apply SetminIE in Hz as []; auto. Qed.

Fact IncludP1 : ∀ A B C, A ⊂ B → A - C ⊂ B - C.
Proof.
  intros * Hab z Hz. apply SetminIE in Hz as []. apply SetminIE; auto.
Qed.

Fact IncludP2 : ∀ A X, X - A ⊂ X.
Proof. intros * x Hx. apply ClaE in Hx. tauto. Qed.

Fact TwSetmin : ∀ A X, A ⊂ X → X - (X - A) = A.
Proof.
  intros. AppE. apply SetminIE in H0 as [Hx H0].
  destruct (classic (x ∈ A)); eauto. elim H0. apply SetminIE. tauto.
  apply SetminIE. split; auto. intro. apply SetminIE in H1 as []; tauto.
Qed.

Fact TwDeMorgan : ∀ A B C, A - (B ∩ C) = (A - B) ⋃ (A - C).
Proof.
  intros. AppE; apply ClaE in H as [_ H].
  - destruct H, (classic (x ∈ C)); apply UnionIE.
    + left; apply SetminIE. split; auto.
      intro; elim H0. apply InterIE. auto.
    + right; apply SetminIE. auto.
  - destruct H; apply SetminIE in H as []; apply SetminIE;
    split; auto; intro; apply InterIE in H1 as []; tauto.
Qed.

Fact InterEqEmI : ∀ x U A,
  Ensemble x → U ∩ A - [x] = ∅ → x ∉ A → U ∩ A = ∅.
Proof with eauto.
  intros. rewrite <- H0. AppE; apply InterIE in H2 as [Hu Ha];
  apply InterIE; split... apply SetminIE. split... intro.
  apply SingE in H2... subst... apply ClaE in Ha. tauto.
Qed.

Definition EleU cA := \{ λ z, ∃ y, z ∈ y ∧ y ∈ cA \}.
Notation "∪ cA" := (EleU cA)(at level 66).

Fact EleUIE : ∀ x cA, (∃ A, x ∈ A ∧ A ∈ cA) ↔ x ∈ ∪cA.
Proof.
  split; intros. destruct H as [A []]. apply ClaI; Ens.
  apply ClaE in H as [Hx [y []]]. eauto.
Qed.

Fact EleUSin : ∀ X, Ensemble X → ∪[X] = X.
Proof with eauto.
  intros * Hxe. AppE. apply EleUIE in H as [y [Hx Hy]].
  apply SingE in Hy... subst... apply EleUIE.
  exists X. split... apply SingI...
Qed.

Axiom EleUAx : ∀ A, Ensemble A → Ensemble (∪A).

Definition EleI cA := \{ λ z, ∀ y, y ∈ cA → z ∈ y \}.
Notation "⋂ cA" := (EleI cA)(at level 66).

(* De Morgan Law *)
Definition AAr A cA := \{λ z, ∃ Ar, Ar ∈ cA ∧ z = A - Ar\}.

Fact AArI : ∀ A B cA, Ensemble A →
  (∃ Ar, Ar ∈ cA ∧ B = A - Ar) → B ∈ AAr A cA.
Proof.
  intros. destruct H0 as [Ar []]. apply ClaI. eapply SubAxI; eauto.
  subst. apply IncludP2. eauto.
Qed.

Fact AArE : ∀ A B cA, B ∈ AAr A cA → (∃ Ar, Ar ∈ cA ∧ B = A - Ar).
Proof. intros. apply ClaE in H. tauto. Qed.

Fact AArP : ∀ A cA, Ensemble A → cA ≠ ∅ → AAr A cA ≠ ∅.
Proof.
  intros. apply EmptyNE in H0 as [Ar H0]. apply EmptyNE.
  exists (A - Ar). apply AArI; eauto.
Qed.

Fact DeMorganUI : ∀ A cA, Ensemble A → cA ≠ ∅ → (A - ∪cA) = ⋂(AAr A cA).
Proof with eauto.
  intros. AppE.
  - apply SetminIE in H1 as [Hx HcA]. apply ClaI; Ens. intros.
    apply AArE in H1 as [B [Hb Heq]]. subst. apply SetminIE.
    split... intro. elim HcA. apply EleUIE...
  - apply EmptyNE in H0 as [Ar H0]. apply ClaE in H1 as []. apply ClaI...
    assert (A - Ar ∈ AAr A cA). apply AArI...
    apply H2 in H3. apply SetminIE in H3 as [Hx H3]. split...
    intro. apply EleUIE in H4 as [B [Hb H4]].
    assert (A - B ∈ AAr A cA). apply AArI...
    apply H2 in H5. apply ClaE in H5; tauto.
Qed.

Axiom InfAx : ∃ y, Ensemble y ∧ ∅ ∈ y ∧ (∀ x, x ∈ y → (x ⋃ [x]) ∈ y).

Fact EmptySet : Ensemble ∅.
Proof. destruct InfAx as [x [_ [He _]]]. Ens. Qed.
Ltac Empt := apply EmptySet.

Fact IntSinEm : ∀ A B C, Ensemble C →
  A ∈ [C] ⋃ [∅] → B ∈ [C] ⋃ [∅] → A ∩ B ∈ [C] ⋃ [∅].
Proof with eauto.
  intros * Hc Ha Hb. apply UnionIE in Ha as [];
  apply UnionIE in Hb as []; apply SingE in H;
  apply SingE in H0; try Empt; subst...
  - rewrite Idem'. apply UnionIE. left; apply ClaI...
  - rewrite EmInter. apply UnionIE. right; apply SingI. Empt.
  - rewrite Commu', EmInter. apply UnionIE.
    right; apply SingI. Empt.
  - rewrite EmInter. apply UnionIE. right. apply SingI. Empt.
Qed.

Fact EleUSinEm : ∀ a cT, Ensemble a → cT ⊂ [a] ⋃ [∅] → ∪cT ∈ [a] ⋃ [∅].
Proof with eauto.
  intros * Hae Ht. assert (Hte : Ensemble cT).
  { eapply SubAxI; [| apply Ht]. apply UnionAx; apply SingEn... Empt. }
  assert (cT ∈ cP([a] ⋃ [∅])). apply ClaI...
  assert (∀ c d, Ensemble c → Ensemble d → cP([c] ⋃ [d]) =
    \{ λ Z, Z = ∅ ∨ Z = [c] ∨ Z = [d] ∨ Z = [c] ⋃ [d] \}).
  { intros. AppE.
    - apply ClaI. Ens. apply ClaE in H2 as [_ H2].
      destruct (classic (c ∈ x)), (classic (d ∈ x)).
      + right; right; right. apply ReSyTrP... intros z Hz.
        apply UnionIE in Hz as []; apply SingE in H5; auto; subst...
      + right; left. AppE; [| apply SingE in H5; subst; auto].
        apply ClaI. Ens. intro. pose proof H5 as H5'.
        apply H2, UnionIE in H5 as []; apply SingE in H5...
        subst; tauto.
      + right; right; left. AppE; [| apply SingE in H5; subst; auto].
        apply ClaI. Ens. intro. pose proof H5 as H5'.
        apply H2, UnionIE in H5 as []; apply SingE in H5...
        subst; tauto.
      + left. AppE; [|exfalso0]. pose proof H5 as H5'.
        apply H2, UnionIE in H5 as []; apply SingE in H5; subst; tauto.
    - apply ClaI. Ens. intros z Hz.
      apply ClaE in H2 as [_ [| [| [| ]]]];
      subst... exfalso0. apply ClaI; Ens. apply ClaI; Ens. }
  rewrite H0 in H; try apply EmptySet... clear H0.
  apply ClaE in H as [_ [| [| [| ]]]]; subst.
  + assert (∪∅ = ∅).
    { AppE; [| exfalso0]. apply EleUIE in H as [y [_ Hy]]. exfalso0. }
    rewrite H. apply UnionIE. right. apply ClaI...
  + rewrite EleUSin... apply UnionIE. left. apply ClaI...
  + pose proof EmptySet. rewrite EleUSin...
    apply UnionIE. right. apply SingI...
  + assert (∪ [a] ⋃ [∅] = a).
    { AppE. apply EleUIE in H as [y [Hx Hy]].
      apply UnionIE in Hy as []; apply SingE in H; subst... exfalso0.
      apply EmptySet. apply EleUIE. exists a. split...
      apply UnionIE. left. apply ClaI... }
    rewrite H. apply UnionIE. left; apply ClaI...
Qed.