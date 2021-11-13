Require Export Topology.

Lemma OpenClosedP : ∀ A B X cT, Ensemble X →
  Topology X cT → A ∈ cT → Closed B X cT → A - B ∈ cT.
Proof with eauto.
  intros * Hxe Ht Ha Hb. pose proof Hb as [_ [Hbx _]].
  apply Theorem3_6 in Hb... assert (A ∩ X - B ∈ cT). apply Ht...
  assert (A ∩ X - B = A - B).
  { AppE. apply InterIE in H0 as []; apply SetminIE.
    apply SetminIE in H1 as []. tauto. apply SetminIE in H0 as [].
    apply InterIE. split... apply SetminIE. split...
    apply Ht, PowerIE in Ha... } rewrite <- H0...
Qed.

Theorem CTYang : ∀ X cT, Ensemble X → Topology X cT →
  (∀ A, A ⊂ X → Closed (Derivaed A X cT) X cT) ↔
  (∀ x, x ∈ X → Closed (Derivaed ([x]) X cT) X cT).
Proof with eauto.
  intros * Hxe Ht. split; intros Hp.
  - intros. apply Hp. intros z Hz. apply SingE in Hz. subst... Ens.
  - intros * Ha. split... split. apply DerivaedP. intros x Hx.
    apply DerivaedIE in Hx as [_ [_ [Hx Hxp]]]. assert (Hop :
       ∀ U, TONeigh x U X cT → U ∩ Derivaed A X cT - [x] ≠ ∅).
    { intros. apply Hxp. apply H. } clear Hxp.
    apply DerivaedIE. split... split... split... intros U' Hu'.
    red in Hu'. apply TNeighP1 in Hu' as [U [Huo Huu]]...
    apply EmptyNE. pose proof Hx as Hx'; apply Hp in Hx; clear Hp.
    assert (Hxn : x ∉ Derivaed ([x]) X cT).
    { intro. apply DerivaedIE in H as [_ [_ [_ H]]]. pose proof Ht as
        [_ [HX _]]. pose proof TNeighP _ _ _ _ Hxe Ht Hx' HX.
      apply H in H0. elim H0. AppE; [| exfalso0].
      apply InterIE in H1 as []. apply SetminIE in H2 as []. tauto. }
    pose proof Huo as [[_ [_ [Hxu _]]] _].
    set (V := U - Derivaed ([x]) X cT).
    assert (Huv : V ⊂ U). { apply IncludP. intros z... }
    assert (Hv : TONeigh x V X cT).
    { destruct Huo as [[_ [_ [_ [Z [Hz [Hxz Huz]]]]]] [_ Huo]].
      split. split... split... split. eapply ReSyTrP...
      exists (Z - Derivaed ([x]) X cT). split. eapply OpenClosedP...
      split. apply ClaI. Ens. tauto. eapply IncludP1...
      split. apply SetminIE. split... eapply OpenClosedP... }
    pose proof Hv as Hv'. apply Hop, EmptyNE in Hv as [y Hv].
    apply InterIE in Hv as [Hyv Hyp]. apply SetminIE in Hyv as
      [Hyu Hyd]. apply SetminIE in Hyp as [Hya Hxy].
    assert (Hnq : y ≠ x). { intro. elim Hxy. apply ClaI; Ens. }
    assert (Hw : ∃ W, W ∈ TNeighS y X cT ∧ x ∉ W).
    { apply DerivaedP1 in Hyd as [W [Hw He]]... exists W. split.
      apply TNeighSIE... apply InterEqEmI in He... intro.
      assert (W ∩ [x] ≠ ∅).
      { apply EmptyNE. exists x. apply InterIE.
        split... apply SingI. Ens. } tauto. Ens. intros z Hz.
      apply SingE in Hz. subst... Ens. }
    destruct Hw as [W [Hw Hxw]]. assert (Hv : V ∈ TNeighS y X cT).
    { apply TNeighSIE... split... split... split. apply IncludP...
      exists (V - Derivaed ([x]) X cT). split. eapply OpenClosedP;
      try apply Hv'... split. apply SetminIE. split...
      apply ClaI; Ens. apply IncludP2. } set (K := W ∩ V).
    assert (Hk : K ∈ TNeighS y X cT). apply Theorem3_4b...
    apply TNeighSIE in Hk... apply DerivaedIE in Hya.
    apply Hya, EmptyNE in Hk as [z Hz].
    apply InterIE in Hz as [Hz Hzp]. apply SetminIE in Hzp as
      [Hza Hzy]. exists z. apply InterIE. assert (Hnq1 : z ≠ x).
    { apply InterIE in Hz as [Hz _]. intro. subst; tauto. }
    split. apply InterIE in Hz as []...
    apply SetminIE. split... intro. apply SingE in H. tauto. Ens.
Qed.