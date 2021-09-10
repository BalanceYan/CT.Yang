Require Export Ensemble.

(* Section 3.1 *)
Definition Topology X cT := cT ⊂ cP(X) ∧
  X ∈ cT ∧ ∅ ∈ cT ∧ (∀ A B, A ∈ cT → B ∈ cT → A ∩ B ∈ cT) ∧
  (∀ cT1, cT1 ⊂ cT → ∪cT1 ∈ cT).

Definition Ordinary X := [X] ⋃ [∅].

Theorem Theorem3_1 : ∀ X, Ensemble X → Topology X (Ordinary X).
Proof with eauto.
  intros * Hxe. pose proof EmptySet as Hee. repeat split...
  - intros A Ha. apply ClaI; Ens. apply UnionIE in Ha as [];
    apply SingE in H; subst... intros x... intros z Hz; exfalso0.
  - apply UnionIE. left; apply ClaI...
  - apply UnionIE. right; apply ClaI...
  - unfold Ordinary. intros. apply IntSinEm...
  - intros. unfold Ordinary. apply EleUSinEm...
Qed.

Definition Discrete X := cP(X).

Theorem Theorem3_2 : ∀ X, Ensemble X → Topology X (Discrete X).
Proof with eauto.
  intros. repeat split. intros A Ha... apply ClaI... intros A...
  apply ClaI. Empt. intros A Ha; exfalso0.
  intros * Ha Hb. apply ClaE in Ha as []; apply ClaE in Hb as [].
  apply ClaI. apply InterEn... intros z Hz.
  apply InterIE in Hz as []... intros. apply ClaI. apply EleUAx.
  apply PowerP in H as []. unfold Discrete in H0. eapply SubAxI...
  intros x Hx. apply ClaE in Hx as [Hxe [A [Hx Ha]]].
  apply H0 in Ha. apply ClaE in Ha as []...
Qed.

(* Section 3.2 *)
Definition TNeigh x U X cT := Topology X cT ∧ x ∈ X ∧ U ⊂ X ∧
  ∃ V, V ∈ cT ∧ x ∈ V ∧ V ⊂ U.

Fact TNeighP : ∀ x U X cT, Ensemble X →
  Topology X cT → x ∈ U → U ∈ cT → TNeigh x U X cT.
Proof with eauto.
  intros * Hxe Ht Hx Hu. split... assert (Hxx : U ⊂ X).
  { apply Ht in Hu. apply PowerIE in Hu... } split... split...
  exists U. repeat split... intros z...
Qed.

Definition TNeighS x X cT := \{λ U, TNeigh x U X cT \}.

Fact TNeighSIE : ∀ x U X cT,
  Ensemble X → TNeigh x U X cT ↔ U ∈ TNeighS x X cT.
Proof.
  split; intros. apply ClaI; auto. eapply SubAxI; eauto. apply H0.
  apply ClaE in H0. tauto.
Qed.

Definition TONeigh x U X cT := TNeigh x U X cT ∧ x ∈ U ∧ U ∈ cT.

Fact TNeighP1 : ∀ x U X cT, Ensemble X → TNeigh x U X cT →
  ∃ V, TONeigh x V X cT ∧ V ⊂ U.
Proof.
  intros * Hxe [Ht [_ [Hv [V [Hvo [Hxv Huv]]]]]].
  exists V. split; auto. split. apply TNeighP; auto. tauto.
Qed.

(* Theorem3_3 *)
Lemma LeTh3_3 : ∀ U, U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}).
Proof with eauto.
  intro. AppE. apply EleUIE. exists [x]. split. apply SingI. Ens.
  apply ClaI. apply SingEn. Ens. exists x. split...
  apply EleUIE in H as [y [Hy Heq]].
  apply ClaE in Heq as [_ [z [Hz Heq]]].
  subst. apply SingE in Hy. subst... Ens.
Qed.

Definition Ux x U cT := ∪\{λ V, x ∈ U ∧ V ∈ cT ∧ x ∈ V ∧ V ⊂ U \}.

Theorem Theorem3_3 : ∀ U X cT, Ensemble X → Topology X cT → U ⊂ X →
  (U ∈ cT ↔ ∀ x, x ∈ U → U ∈ TNeighS x X cT).
Proof with eauto.
  intros * Hxe Ht Hsub. split; intros Hp.
  - intros * Hx. apply TNeighSIE... apply TNeighP...
  - destruct (classic (U = ∅)). subst; apply Ht.
    assert (H1 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}) ⊂
       ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\})).
    { intros z Hz. apply EleUIE in Hz as [y [Hy Hz]].
      apply ClaE in Hz as [_ [x0 [Hx0 Hz]]]. subst...
      apply SingE in Hy; Ens. subst. assert (Hx0' := Hx0).
      apply Hp in Hx0. apply TNeighSIE in Hx0... apply EleUIE. 
      exists (Ux x0 U cT). split. apply EleUIE. assert (Hn := Hx0).
      destruct Hx0 as [_ [_ [_ [V [Hv [Hx0 Hvu]]]]]].
      exists V. split... apply ClaI; Ens. apply ClaI...
      apply (SubAxI U). apply (SubAxI X)... intros z Hz.
      apply EleUIE in Hz as [A [Ha Hz]].
      apply ClaE in Hz as [_ [_ [_ [_ Hz]]]]... }
    assert (H2 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\}) ⊂ U).
    { intros z Hz. apply EleUIE in Hz as [y [Hy Hz]].
      apply ClaE in Hz as [_ [t [Htu Hz]]]. subst... apply EleUIE in
        Hy as [e [Hz Hy]]. apply ClaE in Hy. apply Hy... }
    assert (Hg : U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = Ux x U cT\})).
    { apply ReSyTrP... rewrite <- LeTh3_3 in H1... }
    rewrite Hg. apply Ht. intros V Hv.
    apply ClaE in Hv as [_ [x [Hx Heq]]]. subst.
    apply Ht. intros z Hz. apply ClaE in Hz; tauto.
Qed.

(* Theorem3_4 *)
Theorem Theorem3_4a : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  TNeighS x X cT ≠ ∅ ∧ (∀ U, U ∈ TNeighS x X cT → x ∈ U).
Proof with eauto.
  intros * Hxe Ht Hx. split.
  - assert (X ∈ TNeighS x X cT).
    { apply ClaI... split... split... split. intros z...
      exists X. split. apply Ht. split... intros z... }
    intro. rewrite H0 in H. exfalso0.
  - intros * Hu. apply TNeighSIE in Hu as [_[_[_[V [_[Hv Hsub]]]]]]...
Qed.

Theorem Theorem3_4b : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  (∀ U V, U ∈ TNeighS x X cT → V ∈ TNeighS x X cT →
  U ∩ V ∈ TNeighS x X cT).
Proof with eauto.
  intros * Hxe Ht Hx * Hu Hv.
  apply TNeighSIE in Hu as [_ [_ [Hux [U0 [Ho1 [Hu0 Hsub1]]]]]]...
  apply TNeighSIE in Hv as [_ [_ [Hvx [V0 [Ho2 [Hv0 Hsub2]]]]]]...
  assert (Huv : x ∈ U0 ∩ V0 ∧ U0 ∩ V0 ⊂ U ∩ V).
  { split. apply InterIE. tauto. intros z Hz.
    apply InterIE in Hz as [Hzu Hzv]. apply InterIE. split... }
  apply TNeighSIE... split... split... split. intros z Hz.
  apply InterIE in Hz as [Hz1 _]... exists (U0 ∩ V0).
  split; try apply Ht...
Qed.

Theorem Theorem3_4c : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U V, U ∈ TNeighS x X cT → V ⊂ X → U ⊂ V → V ∈ TNeighS x X cT.
Proof with eauto.
  intros * Hxe Ht Hx * Hu Hv Hsub.
  apply TNeighSIE in Hu as [_ [_ [Hux [U0 [Hou [Hu0 Hsub1]]]]]]...
  apply TNeighSIE... split... split... split...
  exists U0. repeat split... eapply ReSyTrP...
Qed.

Theorem Theorem3_4d : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U, U ∈ TNeighS x X cT → ∃ V, V ∈ TNeighS x X cT ∧ V ⊂ U ∧
  (∀ y, y ∈ V → V ∈ TNeighS y X cT).
Proof with eauto.
  intros * Hxe Ht Hx * Hu. assert (Hu' := Hu).
  apply TNeighSIE in Hu as [_ [_ [Hux [V [Hvo [Hvx Hsub]]]]]]...
  exists V. split. apply TNeighSIE... split... split... split.
  eapply ReSyTrP... exists V. split... split... intros z...
  split... apply Theorem3_3... eapply ReSyTrP...
Qed.

(* Section 3.3 *)
Definition Condensa x A X cT := Topology X cT ∧ A ⊂ X ∧ x ∈ X ∧
  ∀ U, TNeigh x U X cT → U ∩ (A - [x]) ≠ ∅.

Definition Derivaed A X cT := \{λ x, Condensa x A X cT \}.

Fact DerivaedIE : ∀ x A X cT, Condensa x A X cT ↔ x ∈ Derivaed A X cT.
Proof.
  split; intros. apply ClaI; auto. destruct H as [_ [_ [Hx _]]]. Ens.
  apply ClaE in H. tauto.
Qed.

Fact DerivaedP : ∀ A X cT, Derivaed A X cT ⊂ X.
Proof. intros * x Hx. apply ClaE in Hx. apply Hx. Qed.

Fact DerivaedP1 : ∀ x C X cT, Topology X cT → C ⊂ X → x ∈ X →
  x ∉ Derivaed C X cT → ∃ U, TNeigh x U X cT ∧ U ∩ (C - [x]) = ∅.
Proof with eauto.
  intros * Ht Hsub Hx Hp.
  destruct (classic (∃ U, TNeigh x U X cT ∧ U ∩ (C - [x]) = ∅))...
  elim Hp. apply ClaI. Ens. split... split... split...
Qed.

(* Theorem3_5 *)
Theorem Theorem3_5a : ∀ X cT,
  Ensemble X → Topology X cT → Derivaed ∅ X cT = ∅.
Proof with eauto.
  intros * Hxe Ht. AppE; [|exfalso0].
  apply DerivaedIE in H as [_ [_ [Hx Hp]]]. eapply TNeighP in Ht...
  apply Hp in Ht. elim Ht. AppE; [|exfalso0]. apply InterIE in H as
    [_ H]. apply SetminIE in H as []; tauto. apply Ht.
Qed.

Theorem Theorem3_5b : ∀ A B X cT, Ensemble X → Topology X cT →
  A ⊂ X → B ⊂ X → A ⊂ B → Derivaed A X cT ⊂ Derivaed B X cT.
Proof with eauto.
  intros * HXe Ht Ha Hb Hsub. intros x Hx.
  apply DerivaedIE in Hx as [_ [_ [Hx Hp]]]. apply DerivaedIE.
  split... split... split... intros U Hu. apply Hp in Hu.
  assert (U ∩ A - [x] ⊂ U ∩ B - [x]).
  { intros z Hz. apply InterIE in Hz as [Hz Hza].
    apply SetminIE in Hza as [Hza Hneq]. apply InterIE. split...
    apply SetminIE. split... }
  intro. rewrite H0 in H. assert (U ∩ A - [x] = ∅).
  { apply ReSyTrP... intros z Hz. exfalso0. } tauto.
Qed.

Theorem Theorem3_5c : ∀ A B X cT,
  Ensemble X → Topology X cT → A ⊂ X → B ⊂ X →
  Derivaed (A ⋃ B) X cT = Derivaed A X cT ⋃ Derivaed B X cT.
Proof with eauto.
  intros * HXe Ht Ha Hb. assert (A ⊂ A ⋃ B ∧ B ⊂ A ⋃ B).
  { split; intros x Hx; apply UnionIE... }
  destruct H as [Hsa Hsb]. assert (A ⋃ B ⊂ X).
  { intros z Hz. apply UnionIE in Hz as []... }
  eapply Theorem3_5b in Hsa... eapply Theorem3_5b in Hsb...
  AppE; revgoals. apply UnionIE in H0 as []...
  destruct (classic (x ∈ Derivaed A X cT ⋃ Derivaed B X cT))...
  assert (Hab : x ∉ Derivaed A X cT ∧ x ∉ Derivaed B X cT).
  { split; intro; elim H1; apply UnionIE... }
  clear H1; destruct Hab as [Hna Hnb]. assert (H0' := H0).
  apply DerivaedIE in H0' as [_ [_ [Hx _]]].
  apply DerivaedP1 in Hna as [U [Hun Hue]]...
  apply DerivaedP1 in Hnb as [V [Hvn Hve]]...
  set (U ∩ V) as D. assert (Hd : D ∩ ((A ⋃ B) - [x]) = ∅).
  { assert (H1 : D ∩ ((A ⋃ B) - [x]) = D ∩ ((A - [x]) ⋃ (B - [x]))).
    { assert ((A ⋃ B) - [x] = A - [x] ⋃ B - [x]).
      { AppE. apply SetminIE in H1 as [Hab H1].
        apply UnionIE in Hab as []; apply UnionIE.
        left; apply SetminIE... right; apply SetminIE...
        apply UnionIE in H1 as []; apply SetminIE in H1 as [H1 He];
        apply ClaI; Ens; split; auto; apply ClaI; Ens. }
      rewrite H1... }
    assert (H2 : D ∩ (A - [x] ⋃ B - [x]) =
      (D ∩ (A - [x])) ⋃ (D ∩ (B - [x]))).
    { apply DistribuLI... }
    assert (H3 : (D ∩ (A - [x])) ⋃ (D ∩ (B - [x])) ⊂
      (U ∩ (A - [x])) ⋃ (V ∩ (B - [x]))).
    { intros z Hz. apply UnionIE in Hz as []; apply UnionIE;
      apply InterIE in H3 as [H3 Hz]; apply InterIE in H3 as [Hu Hv].
      left; apply InterIE... right; apply InterIE... }
    assert (H4 : (U ∩ (A - [x])) ⋃ (V ∩ (B - [x])) = ∅).
    { rewrite Hue, Hve. AppE.
      apply UnionIE in H4 as []; exfalso0. exfalso0. }
    rewrite H1, H2. rewrite H4 in H3. apply ReSyTrP...
     intros z Hz; exfalso0. }
  assert (x ∉ Derivaed (A ⋃ B) X cT).
  { apply DerivaedIE in H0 as [_ [_ H0]]. assert (D ∈ TNeighS x X cT).
    { apply Theorem3_4b; try (apply ClaI); eauto; apply (SubAxI X _)...
      apply Hun. apply Hvn. }
    apply TNeighSIE in H1... apply H0 in H1; tauto. } tauto.
Qed.

Theorem Theorem2_4_1d : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Derivaed (Derivaed A X cT) X cT ⊂ A ⋃ Derivaed A X cT.
Proof with eauto.
  intros * HXe Ht Hsub x Hx.
  destruct (classic (x ∈ A ⋃ Derivaed A X cT))...
  apply UnionNE in H as [Hxa Hxd]. assert (Hx' := Hx).
  apply DerivaedIE in Hx as [_ [_ [Hx _]]].
  apply DerivaedP1 in Hxd as [U [Hun Hue]]...
  assert (U ∈ TNeighS x X cT). apply TNeighSIE...
  pose proof Theorem3_4d x X cT HXe Ht Hx as Hu.
  apply Hu in H as [V [Htv [Hvu Hp]]]; clear Hu. assert (V ⊂ X).
  { destruct Hun as [_ [_ [Hun _]]]. eapply ReSyTrP... }
  pose proof Theorem3_3 _ _ _ HXe Ht H.
  pose proof Hp as Hp'. apply H0 in Hp; clear H H0.
  assert (V ∩ A - [x] = ∅).
  { AppE; [| exfalso0]. assert (V ∩ A - [x] ⊂ U ∩ A - [x]).
    { intros z Hz. apply InterIE in Hz as []. apply InterIE. split... }
    apply H0 in H. rewrite Hue in H. exfalso0. }
  assert (V ∩ A = ∅). { apply (InterEqEmI x V A); Ens. }
  assert (∀ y, y ∈ V → y ∉ A).
  { intros * Hy Hn. assert (y ∈ V ∩ A). apply InterIE...
    rewrite H0 in H1... exfalso0. }
  assert (∀ y, y ∈ V → V ∩ A - [y] = ∅).
  { intros. AppE; [| exfalso0]. apply InterIE in H3 as [].
    apply SetminIE in H4 as []. apply H1 in H3... tauto. }
  assert (∀ y, y ∈ V → y ∉ Derivaed A X cT).
  { intros. intro. apply DerivaedIE in H4 as [_ [_ [_ H4]]].
    pose proof H3. apply H2 in H3. apply Hp' in H5.
    apply TNeighSIE in H5... apply H4 in H5. tauto. }
  assert (V ∩ Derivaed A X cT - [x] = ∅).
  { AppE; [| exfalso0]. apply InterIE in H4 as [].
    apply H3 in H4. apply SetminIE in H5 as []. tauto. }
  apply DerivaedIE in Hx' as [_ [_ [_ Hx']]]. apply TNeighSIE in Htv...
  apply Hx' in Htv. tauto.
Qed.

(* Section 3.4 *)
Definition Closed A X cT :=
  Topology X cT ∧ A ⊂ X ∧ Derivaed A X cT ⊂ A.

(* Theorem3_6 *)
Theorem Theorem3_6 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closed A X cT ↔ X - A ∈ cT.
Proof with eauto.
  intros * HXe Ht Hsub. pose proof (IncludP2 A X) as Hsub'.
  split; intros Hp.
  - destruct Hp as [_ [_ Hp]]. eapply Theorem3_3...
    intros * Hx. apply SetminIE in Hx as [Hx Hn].
    assert (x ∉ Derivaed A X cT). { intro. apply Hp in H; tauto. }
    apply DerivaedP1 in H as
      [U [[_ [_ [Hus [V [Hvo [Hvx Hvu]]]]]] Hue]]...
    apply (InterEqEmI x _ _) in Hue; Ens. assert (U ⊂ X - A).
    { intros z Hz. apply SetminIE. split... intro.
      assert (z ∈ U ∩ A). apply InterIE...
      rewrite Hue in H0. exfalso0. }
    apply TNeighSIE... split... split... split...
    exists V. split... split... eapply ReSyTrP...
  - assert (∀ x, x ∈ X-A → TNeigh x (X-A) X cT ∧ x ∉ Derivaed A X cT).
    { intros x Hx. apply (Theorem3_3 (X-A) _ _) in Ht...
      eapply Ht in Hp... apply TNeighSIE in Hp... split...
      intro. apply ClaE in H as [_ [_ [_ [_ H0]]]]. apply H0 in Hp.
      assert (X - A ∩ A - [x] = ∅).
      { AppE; [| exfalso0]. apply InterIE in H as [Hn H].
        apply SetminIE in Hn. apply SetminIE in H; tauto. } tauto. }
    split... split... intros x Hx. destruct (classic (x ∈ A))...
    assert (x ∈ X - A). { apply DerivaedIE in Hx as [_ [_ [Hx _]]].
      apply SetminIE... } apply H in H1 as [_ H1]; tauto.
Qed.

(* Theorem3_7 *)
Definition cF X cT := \{λ U, U ⊂ X ∧ X - U ∈ cT \}.

Fact cFIE : ∀ U X cT, Ensemble X → U ⊂ X ∧ X - U ∈ cT ↔ U ∈ cF X cT.
Proof.
  split; intros. apply ClaI; auto. apply (SubAxI X U); tauto.
  apply ClaE in H0. tauto.
Qed.

Fact cFP : ∀ X cT, Ensemble X → cF X cT ⊂ cP(X).
Proof.
  intros * HXe U Hu. apply ClaE in Hu. apply PowerIE; tauto.
Qed.

Theorem Theorem3_7a : ∀ X cT, Ensemble X → Topology X cT →
  X ∈ cF X cT ∧ ∅ ∈ cF X cT.
Proof with eauto.
  intros * Hxe Ht. split.
  - apply cFIE... split. intros z... rewrite SetminId. apply Ht.
  - apply ClaI. Empt. split. intros z Hz; exfalso0.
    rewrite SetminEm. apply Ht.
Qed.

Theorem Theorem3_7b : ∀ A B X cT, Ensemble X → Topology X cT →
  A ∈ cF X cT → B ∈ cF X cT → A ⋃ B ∈ cF X cT.
Proof with eauto.
  intros * He Ht Ha Hb. apply cFIE in Ha as [Ha Hac]...
  apply cFIE in Hb as [Hb Hbc]... assert (X - A ∩ X - B ∈ cT).
  apply Ht... apply TwSetmin in Ha. apply TwSetmin in Hb.
  rewrite <- Ha, <- Hb.
  assert (X - (X - A) ⋃ X - (X - B) = X - (X - A ∩ X - B)).
  { AppE. rewrite TwDeMorgan; apply UnionIE;
    apply UnionIE in H0 as []... rewrite TwDeMorgan in H0... }
  rewrite H0. apply (cFIE _ X cT)... split. apply IncludP2.
  rewrite TwSetmin... intros z Hz. apply InterIE in Hz as [_ Hz].
  apply SetminIE in Hz; tauto.
Qed.

Theorem Theorem3_7c : ∀ cF1 X cT, Ensemble X →
  Topology X cT → cF1 ≠ ∅ -> cF1 ⊂ cF X cT → ⋂cF1 ∈ cF X cT.
Proof with eauto.
  intros cF1 * HXe Ht Hne Hsub.
  set \{λ A, A ⊂ X ∧ X - A ∈ cF1 \} as cT1. assert (HcT : cT1 ⊂ cT).
  { intros A Ha. apply ClaE in Ha as [_ [Hsa Ha]]. apply Hsub in Ha.
    apply cFIE in Ha as [Hc Ha]... rewrite TwSetmin in Ha... }
  apply Ht in HcT. assert (H4 : (X - ∪cT1) ∈ cF X cT).
  { apply (cFIE _ X cT)... split. apply IncludP2.
    rewrite TwSetmin... apply Ht in HcT. apply PowerIE in HcT... }
  assert (H3 : (X - ∪(AAr X cF1)) = (X - ∪cT1)).
  { AppE; apply SetminIE in H as [Hx Hn]; apply SetminIE; split...
    - intro. elim Hn. apply EleUIE in H as [B [Hb Hbt]].
      apply ClaE in Hbt as [_ [Hbs Hb']]. apply EleUIE.
      exists (X - (X - B)). split. rewrite TwSetmin... apply AArI...
    - intro. elim Hn; clear Hn. apply EleUIE in H as [B [Hb Hbt]].
      pose proof Hbt. apply AArE in Hbt as [T [Hbt Heq]].
      apply EleUIE. exists B. split... apply ClaI... Ens. split; subst.
      apply IncludP2. rewrite TwSetmin... apply Hsub in Hbt.
      apply ClaE in Hbt; tauto. }
  rewrite DeMorganUI in H3; try apply AArP...
  assert (⋂ cF1 = ⋂ AAr X (AAr X cF1)).
  { AppE; apply ClaE in H as []; apply ClaI; auto; intros.
    - apply ClaE in H1 as [_ [B [Hb Heq]]]. apply ClaE in Hb as
        [_ [C [Hc Heq1]]]. apply H0. subst. rewrite TwSetmin...
      apply Hsub in Hc. apply ClaE in Hc; tauto.
    - assert (y ⊂ X). { apply Hsub in H1. apply ClaE in H1; tauto. }
      apply H0. apply ClaI. Ens. exists (X - y). split.
      apply (AArI X _  cF1)... rewrite TwSetmin... } rewrite H, H3...
Qed.
