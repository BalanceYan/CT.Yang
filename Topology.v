Require Export Ensemble.

(* Section 3.1 *)
Definition Topology X cT := cT ⊂ cP(X) ∧
  X ∈ cT ∧ ∅ ∈ cT ∧ (∀ A B, A ∈ cT → B ∈ cT → A ∩ B ∈ cT) ∧
  (∀ cT1, cT1 ⊂ cT → ∪cT1 ∈ cT).

Definition Ordinary X := [X] ⋃ [∅].

Lemma LeTh3_1 : ∀ A B C,
  A ∈ [C] ⋃ [∅] → B ∈ [C] ⋃ [∅] → A ∩ B ∈ [C] ⋃ [∅].
Proof with eauto.
  intros. apply ClaE in H as []; apply ClaE in H0 as [];
  apply ClaE in H; apply ClaE in H0; subst; apply ClaI.
  rewrite Idem'; left; apply ClaI...
  rewrite EmInter; right; apply ClaI...
  right. rewrite Commu', EmInter. apply ClaI...
  right. rewrite EmInter. apply ClaI...
Qed.

Lemma Le1Th3_1 : ∀ X, ∪[X] = X.
Proof with eauto.
  intro. AppE. apply ClaE in H as [y [Hx Hy]]. apply ClaE in Hy.
  subst... apply ClaI. exists X. split... apply ClaI...
Qed.

Lemma Le2Th3_1 : ∀ a cT, cT ⊂ [a] ⋃ [∅] → ∪cT ∈ [a] ⋃ [∅].
Proof with eauto.
  intros. assert (cT ∈ cP([a] ⋃ [∅])); apply ClaI...
  assert (∀ c d, cP([c] ⋃ [d]) =
    \{ λ Z, Z = ∅ \/ Z = [c] \/ Z = [d] \/ Z = [c] ⋃ [d] \}).
  { intros. AppE.
    - apply ClaI. apply ClaE in H1. destruct (classic (c ∈ x)).
      + destruct (classic (d ∈ x)).
        * right; right; right. apply ReSyTrP... split...
          intros z Hz. subst. apply ClaE in Hz as [];
          apply ClaE in H4; subst...
        * right; left. AppE; [| apply ClaE in H4; subst; auto].
          apply ClaI. pose proof H4. apply H1 in H4. subst.
          apply ClaE in H4 as []; apply ClaE in H4; subst... tauto.
      + destruct (classic (d ∈ x)).
        * right; right; left. AppE; [| apply ClaE in H4; subst; auto].
          apply ClaI. pose proof H4. apply H1 in H4. subst.
          apply ClaE in H4 as []; apply ClaE in H4; subst... tauto.
        * left. AppE; [| exfalso0]. pose proof H4. apply H1 in H4.
          subst. apply ClaE in H4 as []; apply ClaE in H4; subst; tauto...
    - apply ClaE in H1. apply ClaI; intros z Hz.
      destruct H1 as [| [| [| ]]]; subst... exfalso0.
      apply ClaI... apply ClaI... } rewrite H1 in H0; clear H1.
  apply ClaE in H0 as [| [| [| ]]]; subst.
  + assert (∪∅ = ∅).
    { AppE; [| exfalso0]. apply ClaE in H0 as [y [_ Hy]]. exfalso0. }
    rewrite H0. right. apply ClaI...
  + left. rewrite Le1Th3_1. apply ClaI...
  + right. rewrite Le1Th3_1. apply ClaI...
  + assert (∪ [a] ⋃ [∅] = a).
    { AppE. apply ClaE in H0 as [y [Hx Hy]].
      apply ClaE in Hy as []; apply ClaE in H0; subst... exfalso0.
      apply ClaI. exists a. split... apply ClaI. left. apply ClaI... }
    rewrite H0. left; apply ClaI...
Qed.

Theorem Theorem3_1 : ∀ X, Topology X (Ordinary X).
Proof with eauto.
  intros. repeat split.
  - intros A Ha. apply ClaE in Ha as []; apply ClaE in H; apply ClaI;
    subst; intros z Hz... exfalso0.
  - apply ClaI. left; apply ClaI...
  - apply ClaI. right; apply ClaI...
  - unfold Ordinary. intros. apply LeTh3_1...
  - intros. unfold Ordinary. apply Le2Th3_1...
Qed.

Definition Discrete X := cP(X).

Theorem Theorem3_2 : ∀ X, Topology X (Discrete X).
Proof with eauto.
  intros. repeat split. intros A Ha... apply ClaI; intros A Ha...
  apply ClaI; intros A Ha; exfalso0.
  intros * Ha Hb. apply ClaE in Ha; apply ClaE in Hb. apply ClaI.
  intros z Hz. apply ClaE in Hz as [H _]...
  intros. apply ClaI. intros x Hx. apply ClaE in Hx as [A [Hx Ha]].
  apply H in Ha. apply ClaE in Ha...
Qed.

(* Section 3.2 *)
Definition TNeigh x U X cT := Topology X cT ∧ x ∈ X ∧ U ⊂ X ∧
  ∃ V, V ∈ cT ∧ x ∈ V ∧ V ⊂ U.

Definition TNeighS x X cT := \{λ U, TNeigh x U X cT \}.

Definition TONeigh x U X cT := TNeigh x U X cT ∧ x ∈ U ∧ U ∈ cT.

Corollary TNeighP : ∀ x U X cT,
  Topology X cT → x ∈ U → U ∈ cT → TNeigh x U X cT.
Proof with eauto.
  intros * Ht Hx Hu. split... assert (Hxx : U ⊂ X).
  { apply Ht in Hu. apply ClaE in Hu... } split... split...
  exists U. repeat split... intros z Hz...
Qed.

Corollary TNeighP1 : ∀ x U X cT, TNeigh x U X cT →
  ∃ V, TONeigh x V X cT ∧ V ⊂ U.
Proof.
  intros * [Ht [_ [Hv [V [Hvo [Hxv Huv]]]]]].
  exists V. split; auto. split. apply TNeighP; auto. tauto.
Qed.

(* Theorem3_3 *)
Lemma LeTh3_3 : ∀ U, U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}).
Proof with eauto.
  intro. AppE. apply ClaI. exists [x]. split. apply SingI...
  apply ClaI. exists x. split... apply ClaE in H as [y [Hy Heq]].
  apply ClaE in Heq as [z [Hz Heq]]. subst. apply SingE in Hy. subst...
Qed.

Definition Ux x U cT := ∪\{λ V, x ∈ U ∧ V ∈ cT ∧ x ∈ V ∧ V ⊂ U \}.

Theorem Theorem3_3 : ∀ U X cT, Topology X cT → U ⊂ X →
  (U ∈ cT ↔ ∀ x, x ∈ U → U ∈ TNeighS x X cT).
Proof with eauto.
  intros * Ht Hsub. split; intros Hp.
  - intros * Hx. apply ClaI. apply TNeighP...
  - destruct (classic (U = ∅)). subst; apply Ht.
    assert (H1 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}) ⊂
       ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\})).
    { intros z Hz. apply ClaE in Hz as [y [Hy Hz]]. apply ClaE
        in Hz as [x0 [Hx0 Hz]]. subst... apply ClaE in Hy. subst...
      assert (Hx0' := Hx0). apply Hp in Hx0. apply ClaE in Hx0.
      apply ClaI. exists (Ux x0 U cT). split. apply ClaI.
      assert (Hn := Hx0). destruct Hx0 as [_ [_ [_ [V [Hv [Hx0 Hvu]]]]]].
      exists V. split... apply ClaI... apply ClaI... }
    assert (H2 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\}) ⊂ U).
    { intros z Hz. apply ClaE in Hz as [y [Hy Hz]].
      apply ClaE in Hz as [t [Htu Hz]]. subst...
      apply ClaE in Hy as [e [Hz Hy]]. apply ClaE in Hy. apply Hy... }
    assert (Hg : U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\})).
    { apply ReSyTrP... split... rewrite <- LeTh3_3 in H1... }
    rewrite Hg. apply Ht. intros V Hv.
    apply ClaE in Hv as [x [Hx Heq]]. subst.
    apply Ht. intros z Hz. apply ClaE in Hz; tauto.
Qed.

(* Theorem3_4 *)
Theorem Theorem3_4a : ∀ x X cT, Topology X cT → x ∈ X →
  TNeighS x X cT ≠ ∅ ∧ (∀ U, U ∈ TNeighS x X cT → x ∈ U).
Proof with eauto.
  intros * Ht Hx. split.
  - assert (X ∈ TNeighS x X cT).
    { apply ClaI. split... split... split. intros z Hz...
      exists X. split. apply Ht. split... intros z Hz... }
    intro. rewrite H0 in H. exfalso0.
  - intros * Hu. apply ClaE in Hu as [_ [_ [_ [V [_ [Hv Hsub]]]]]]...
Qed.

Theorem Theorem3_4b : ∀ x X cT, Topology X cT → x ∈ X →
  (∀ U V, U ∈ TNeighS x X cT → V ∈ TNeighS x X cT →
  U ∩ V ∈ TNeighS x X cT).
Proof with eauto.
  intros * Ht Hx * Hu Hv.
  apply ClaE in Hu as [_ [_ [Hux [U0 [Ho1 [Hu0 Hsub1]]]]]].
  apply ClaE in Hv as [_ [_ [Hvx [V0 [Ho2 [Hv0 Hsub2]]]]]].
  assert (Huv : x ∈ U0 ∩ V0 ∧ U0 ∩ V0 ⊂ U ∩ V).
  { split. apply ClaI; tauto. intros z Hz.
    apply ClaE in Hz as [Hzu Hzv]. apply ClaI. split... }
  apply ClaI. split... split... split. intros z Hz.
  apply ClaE in Hz as [Hz1 _]... exists (U0 ∩ V0).
  split; try apply Ht...
Qed.

Theorem Theorem3_4c : ∀ x X cT, Topology X cT → x ∈ X →
  ∀ U V, U ∈ TNeighS x X cT → V ⊂ X → U ⊂ V → V ∈ TNeighS x X cT.
Proof with eauto.
  intros * Ht Hx * Hu Hv Hsub.
  apply ClaE in Hu as [_ [_ [Hux [U0 [Hou [Hu0 Hsub1]]]]]].
  apply ClaI. split... split... split...
  exists U0. repeat split... eapply ReSyTrP...
Qed.

Theorem Theorem3_4d : ∀ x X cT, Topology X cT → x ∈ X →
  ∀ U, U ∈ TNeighS x X cT → ∃ V, V ∈ TNeighS x X cT ∧ V ⊂ U ∧
  (∀ y, y ∈ V → V ∈ TNeighS y X cT).
Proof with eauto.
  intros * Ht Hx * Hu. assert (Hu' := Hu).
  apply ClaE in Hu as [_ [_ [Hux [V [Hvo [Hvx Hsub]]]]]].
  exists V. split. apply ClaI. split... split... split.
  eapply ReSyTrP... exists V. split... split... intros z HZ...
  split... apply Theorem3_3... eapply ReSyTrP...
Qed.

(* Section 3.3 *)
Definition Condensa x A X cT := Topology X cT ∧ A ⊂ X ∧ x ∈ X ∧
  ∀ U, TNeigh x U X cT → U ∩ (A - [x]) ≠ ∅.

Definition Derivaed A X cT := \{λ x, Condensa x A X cT \}.

Corollary DerivaedP : ∀ A X cT, Derivaed A X cT ⊂ X.
Proof. intros * x Hx. apply ClaE in Hx. apply Hx. Qed.

Corollary DerivaedP1 : ∀ x C X cT, Topology X cT → C ⊂ X → x ∈ X →
  x ∉ Derivaed C X cT → ∃ U, TNeigh x U X cT ∧ U ∩ (C - [x]) = ∅.
Proof with eauto.
  intros * Ht Hsub Hx Hp.
  destruct (classic (∃ U, TNeigh x U X cT ∧ U ∩ (C - [x]) = ∅))...
  elim Hp. apply ClaI. split... split... split...
Qed.

(* Theorem3_5 *)
Theorem Theorem3_5a : ∀ X cT, Topology X cT → Derivaed ∅ X cT = ∅.
Proof with eauto.
  intros * Ht. AppE; [|exfalso0]. apply ClaE in H as [_ [_ [Hx Hp]]].
  eapply TNeighP in Ht... apply Hp in Ht. elim Ht. AppE; [|exfalso0].
  apply ClaE in H as [_ H]. apply ClaE in H; tauto. apply Ht.
Qed.

Theorem Theorem3_5b : ∀ A B X cT, Topology X cT → A ⊂ X → B ⊂ X →
  A ⊂ B → Derivaed A X cT ⊂ Derivaed B X cT.
Proof with eauto.
  intros * Ht Ha Hb Hsub. intros x Hx.
  apply ClaE in Hx as [_ [_ [Hx Hp]]]. apply ClaI. split... split...
  split... intros U Hu. apply Hp in Hu.
  assert (U ∩ A - [x] ⊂ U ∩ B - [x]).
  { intros z Hz. apply ClaE in Hz as [Hz Hza]. apply ClaE in Hza
      as [Hza Hneq]. apply ClaI. split... apply ClaI. split... }
  intro. rewrite H0 in H. assert (U ∩ A - [x] = ∅).
  { apply ReSyTrP... split... intros z Hz. exfalso0. } tauto.
Qed.

Lemma LeTh3_5 : ∀ A B C, A ∩ (B ⋃ C) = A ∩ B ⋃ A ∩ C.
Proof.
  intros. rewrite Commu', Distribu, Commu', (Commu' A C); auto.
Qed.

Theorem Theorem3_5c : ∀ A B X cT, Topology X cT → A ⊂ X → B ⊂ X →
  Derivaed (A ⋃ B) X cT = Derivaed A X cT ⋃ Derivaed B X cT.
Proof with eauto.
  intros * Ht Ha Hb. assert (A ⊂ A ⋃ B ∧ B ⊂ A ⋃ B).
  { split; intros x Hx; apply ClaI. left... right... }
  destruct H as [Hsa Hsb]. assert (A ⋃ B ⊂ X).
  { intros z Hz. apply ClaE in Hz as []... }
  eapply Theorem3_5b in Hsa... eapply Theorem3_5b in Hsb...
  AppE; revgoals. apply ClaE in H0 as []...
  destruct (classic (x ∈ Derivaed A X cT ⋃ Derivaed B X cT))...
  assert (Hab : x ∉ Derivaed A X cT ∧ x ∉ Derivaed B X cT).
  { split; intro; elim H1; apply ClaI... }
  clear H1; destruct Hab as [Hna Hnb]. assert (H0' := H0).
  apply ClaE in H0' as [_ [_ [Hx _]]].
  apply DerivaedP1 in Hna as [U [Hun Hue]]...
  apply DerivaedP1 in Hnb as [V [Hvn Hve]]...
  set (U ∩ V) as D. assert (Hd : D ∩ ((A ⋃ B) - [x]) = ∅).
  { assert (H1 : D ∩ ((A ⋃ B) - [x]) = D ∩ ((A - [x]) ⋃ (B - [x]))).
    { assert ((A ⋃ B) - [x] = A - [x] ⋃ B - [x]).
      { AppE. apply ClaE in H1 as [Hab H1]. apply ClaE in Hab as [];
        apply ClaI. left; apply ClaI... right; apply ClaI...
        apply ClaE in H1 as []; apply ClaE in H1 as [H1 He];
        apply ClaI; split; eauto; apply ClaI; eauto. } rewrite H1... }
    assert (H2 : D ∩ (A - [x] ⋃ B - [x]) =
      (D ∩ (A - [x])) ⋃ (D ∩ (B - [x]))).
    { apply LeTh3_5... }
    assert (H3 : (D ∩ (A - [x])) ⋃ (D ∩ (B - [x])) ⊂
      (U ∩ (A - [x])) ⋃ (V ∩ (B - [x]))).
    { intros z Hz. apply ClaE in Hz as []; apply ClaI;
      apply ClaE in H3 as [H3 Hz]; apply ClaE in H3 as [Hu Hv].
      left; apply ClaI... right; apply ClaI... }
    assert (H4 : (U ∩ (A - [x])) ⋃ (V ∩ (B - [x])) = ∅).
    { rewrite Hue, Hve. AppE.
      apply ClaE in H4 as []; exfalso0. exfalso0. }
    rewrite H1, H2. rewrite H4 in H3. apply ReSyTrP...
    split... intros z Hz; exfalso0. }
  assert (x ∉ Derivaed (A ⋃ B) X cT).
  { apply ClaE in H0 as [_ [_ [_ H0]]]. assert (D ∈ TNeighS x X cT).
    { apply Theorem3_4b; try (apply ClaI)... }
    apply ClaE in H1. apply H0 in H1; tauto. } tauto.
Qed.

Lemma Le1Th3_5 : ∀ x A B, x ∉ A ⋃ B -> x ∉ A /\ x ∉ B.
Proof. intros. split; intro; elim H; apply ClaI; auto. Qed.

Lemma Le2Th3_5 : ∀ x U A, U ∩ A - [x] = ∅ → x ∉ A → U ∩ A = ∅.
Proof with eauto.
  intros. rewrite <- H. AppE; apply ClaE in H1 as [Hu Ha];
  apply ClaI; split... apply ClaI. split... intro.
  apply ClaE in H1. subst... apply ClaE in Ha. tauto.
Qed.

Theorem Theorem2_4_1d : ∀ A X cT, Topology X cT → A ⊂ X →
  Derivaed (Derivaed A X cT) X cT ⊂ A ⋃ Derivaed A X cT.
Proof with eauto.
  intros * Ht Hsub x Hx. destruct (classic (x ∈ A ⋃ Derivaed A X cT))...
  apply Le1Th3_5 in H as [Hxa Hxd].
  assert (Hx' := Hx); apply ClaE in Hx as [_ [_ [Hx _]]].
  apply DerivaedP1 in Hxd as [U [Hun Hue]]...
  assert (U ∈ TNeighS x X cT) by (apply ClaI; auto).
  pose proof Theorem3_4d x X cT Ht Hx as Hu.
  apply Hu in H as [V [Htv [Hvu Hp]]]; clear Hu. assert (V ⊂ X).
  { destruct Hun as [_ [_ [Hun _]]]. eapply ReSyTrP... }
  pose proof Theorem3_3 _ _ _ Ht H.
  pose proof Hp as Hp'. apply H0 in Hp; clear H H0.
  assert (V ∩ A - [x] = ∅).
  { AppE; [| exfalso0]. assert (V ∩ A - [x] ⊂ U ∩ A - [x]).
    { intros z Hz. apply ClaE in Hz as []. apply ClaI. split... }
    apply H0 in H. rewrite Hue in H. exfalso0. }
  assert (V ∩ A = ∅). { eapply Le2Th3_5... }
  assert (∀ y, y ∈ V → y ∉ A).
  { intros * Hy Hn. assert (y ∈ V ∩ A). { apply ClaI... }
    rewrite H0 in H1... exfalso0. }
  assert (∀ y, y ∈ V → V ∩ A - [y] = ∅).
  { intros. AppE; [| exfalso0]. apply ClaE in H3 as [].
    apply ClaE in H4 as []. apply H1 in H3... tauto. }
  assert (∀ y, y ∈ V → y ∉ Derivaed A X cT).
  { intros. intro. apply ClaE in H4 as [_ [_ [_ H4]]].
    pose proof H3. apply H2 in H3. apply Hp' in H5.
    apply ClaE in H5. apply H4 in H5. tauto. }
  assert (V ∩ Derivaed A X cT - [x] = ∅).
  { AppE; [| exfalso0]. apply ClaE in H4 as [].
    apply H3 in H4. apply ClaE in H5 as []. tauto. }
  apply ClaE in Hx' as [_ [_ [_ Hx']]]. apply ClaE in Htv.
  apply Hx' in Htv. tauto.
Qed.

(* Section 3.4 *)
Definition Closed A X cT :=
  Topology X cT ∧ A ⊂ X ∧ Derivaed A X cT ⊂ A.

(* Theorem3_6 *)
Lemma LeTh3_6 : ∀ x U A, U ∩ A - [x] = ∅ → x ∉ A → U ∩ A = ∅.
Proof with eauto.
  intros. rewrite <- H. AppE; apply ClaE in H1 as [Hu Ha];
  apply ClaI; split... apply ClaI. split... intro.
  apply ClaE in H1. subst... apply ClaE in Ha. tauto.
Qed.

Theorem Theorem3_6 : ∀ A X cT, Topology X cT → A ⊂ X →
  Closed A X cT ↔ X - A ∈ cT.
Proof with eauto.
  intros * Ht Hsub. apply IncludP2 in Hsub as Hsub'. split; intros Hp.
  - destruct Hp as [_ [_ Hp]]. eapply Theorem3_3...
    intros * Hx. apply ClaE in Hx as [Hx Hn].
    assert (x ∉ Derivaed A X cT). { intro. apply Hp in H; tauto. }
    apply DerivaedP1 in H as
      [U [[_ [_ [Hus [V [Hvo [Hvx Hvu]]]]]] Hue]]...
    apply LeTh3_6 in Hue... assert (U ⊂ X - A).
    { intros z Hz. apply ClaI. split... intro. assert (z ∈ U ∩ A).
      { apply ClaI... } rewrite Hue in H0. exfalso0. }
    apply ClaI. split... split... split...
    exists V. split... split... eapply ReSyTrP. split...
  - assert (∀ x, x ∈ X - A → TNeigh x (X - A) X cT ∧
      x ∉ Derivaed A X cT).
    { intros x Hx. apply (Theorem3_3 (X-A) _ _) in Ht...
      eapply Ht in Hp... apply ClaE in Hp... split...
      intro. apply ClaE in H as [_ [_ [_ H0]]]. apply H0 in Hp.
      assert (X - A ∩ A - [x] = ∅). { AppE; [| exfalso0].
        apply ClaE in H as [Hn H]. apply ClaE in Hn.
        apply ClaE in H; tauto. } tauto. }
    split... split... intros x Hx. destruct (classic (x ∈ A))...
    assert (x ∈ X - A). { apply ClaE in Hx as [_ [_ [Hx _]]].
      apply ClaI... } apply H in H1 as [_ H1]; tauto.
Qed.

(* Theorem3_7 *)
Definition cF X cT := \{λ U, U ⊂ X ∧ X - U ∈ cT \}.

Corollary cFP : ∀ X cT, cF X cT ⊂ cP(X).
Proof.
  intros * U Hu. apply ClaE in Hu. apply ClaI; tauto.
Qed.

Lemma Le1Th3_7 : ∀ X, X - X = ∅.
Proof. intro. AppE. apply ClaE in H; tauto. exfalso0. Qed.

Lemma Le2Th3_7 : ∀ X, X - ∅ = X.
Proof.
  intro. AppE. apply ClaE in H; tauto.
  apply ClaI. split; auto. intro. exfalso0.
Qed.

Theorem Theorem3_7a : ∀ X cT, Topology X cT →
  X ∈ cF X cT ∧ ∅ ∈ cF X cT.
Proof with eauto.
  intros * Ht. split.
  - apply ClaI. split. intros z Hz... rewrite Le1Th3_7. apply Ht.
  - apply ClaI. split. intros z Hz; exfalso0.
    rewrite Le2Th3_7. apply Ht.
Qed.

Theorem Theorem3_7b : ∀ A B X cT, Topology X cT →
  A ∈ cF X cT → B ∈ cF X cT → A ⋃ B ∈ cF X cT.
Proof with eauto.
  intros * Ht Ha Hb. apply ClaE in Ha as [Ha Hac].
  apply ClaE in Hb as [Hb Hbc]. assert (X - A ∩ X - B ∈ cT).
  { apply Ht... } apply TwSetmin in Ha.
  apply TwSetmin in Hb. rewrite <- Ha, <- Hb. 
  assert (X - (X - A) ⋃ X - (X - B) = X - (X - A ∩ X - B)).
  { AppE. rewrite TwDeMorgan; apply ClaI;
    apply ClaE in H0 as []... rewrite TwDeMorgan in H0;
    apply ClaI; apply ClaE in H0 as []... } rewrite H0.
  apply ClaI. split. intros z Hz. apply ClaE in Hz; tauto.
  rewrite TwSetmin... intros z Hz. apply ClaE in Hz as [_ Hz].
  apply ClaE in Hz; tauto.
Qed.

Theorem Theorem3_7c : ∀ cF1 X cT, Topology X cT → cF1 ≠ ∅ ->
  cF1 ⊂ cF X cT → ⋂cF1 ∈ cF X cT.
Proof with eauto.
  intros cF1 * Ht Hne Hsub. set \{λ A, A ⊂ X ∧ X - A ∈ cF1 \} as cT1.
  assert (HcT : cT1 ⊂ cT).
  { intros A Ha. apply ClaE in Ha as [Hsa Ha]. apply Hsub in Ha.
    apply ClaE in Ha as [Hc Ha]. rewrite TwSetmin in Ha... }
  apply Ht in HcT. assert (H4 : (X - ∪cT1) ∈ cF X cT).
  { apply ClaI. split. intros x Hx. apply ClaE in Hx; tauto.
    rewrite TwSetmin... apply Ht in HcT. apply ClaE in HcT... }
  assert (H3 : (X - ∪(AAr X cF1)) = (X - ∪cT1)).
  { AppE; apply ClaE in H as [Hx Hn]; apply ClaI; split...
    - intro. elim Hn. apply ClaE in H as [B [Hb Hbt]].
      apply ClaE in Hbt as [Hbs Hb']. apply ClaI. exists (X - (X - B)).
      split. rewrite TwSetmin... apply ClaI...
    - intro. elim Hn; clear Hn. apply ClaE in H as [B [Hb Hbt]].
      apply ClaE in Hbt as [T [Hbt Heq]]. apply ClaI. exists B.
      split... apply ClaI. split; subst.
      + intros z Hz. apply ClaE in Hz; tauto.
      + rewrite TwSetmin... apply Hsub in Hbt.
        apply ClaE in Hbt; tauto. }
  rewrite DeMorganUI in H3; try apply AArP...
  assert (⋂ cF1 = ⋂ AAr X (AAr X cF1)).
  { AppE; apply ClaE in H; apply ClaI; intros.
    - apply ClaE in H0 as [B [Hb Heq]]. apply ClaE in Hb as
        [C [Hc Heq1]]. apply H. subst. rewrite TwSetmin...
      apply Hsub in Hc. apply ClaE in Hc; tauto.
    - assert (y ⊂ X). { apply Hsub in H0. apply ClaE in H0; tauto. }
      apply H. apply ClaI. exists (X - y). split. apply ClaI...
      rewrite TwSetmin... } rewrite H, H3...
Qed.
