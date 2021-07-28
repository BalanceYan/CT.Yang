Require Export Topology.

Lemma OpenClosedP : ∀ A B X cT,
  Topology X cT → A ∈ cT → Closed B X cT → A - B ∈ cT.
Proof with eauto.
  intros * Ht Ha Hb. pose proof Hb as [_ [Hbx _]].
  apply Theorem3_6 in Hb...
  assert (A ∩ X - B ∈ cT). { apply Ht... }
  assert (A ∩ X - B = A - B).
  { AppE; apply ClaE in H0 as []; apply ClaI. apply ClaE in H1 as [].
    tauto. split... apply ClaI. split... apply Ht, ClaE in Ha... }
  rewrite <- H0...
Qed.

Theorem YangZhongDao : ∀ X cT, Topology X cT →
  (∀ A, A ⊂ X → Closed (Derivaed A X cT) X cT) ↔
  (∀ x, x ∈ X → Closed (Derivaed ([x]) X cT) X cT).
Proof with eauto.
  intros * Ht. split; intros Hp.
  - intros. apply Hp. intros z Hz. apply ClaE in Hz. subst...
  - intros * Ha. split... split. apply DerivaedP. intros x Hx.
    apply ClaE in Hx as [_ [_ [Hx Hxp]]].
    assert (Hop : ∀ U, TONeigh x U X cT → U ∩ Derivaed A X cT - [x] ≠ ∅).
    { intros. apply Hxp. apply H. } clear Hxp.
    apply ClaI. split... split... split...
    intros U' Hu'. red in Hu'. apply TNeighP1 in Hu' as [U [Huo Huu]].
    apply EmptyNE. pose proof Hx as Hx'; apply Hp in Hx; clear Hp.
    assert (Hxn : x ∉ Derivaed ([x]) X cT).
    { intro. apply ClaE in H as [_ [_ [_ H]]].
      pose proof Ht as [_ [HX _]]. pose proof TNeighP _ _ _ _ Ht Hx' HX.
      apply H in H0. elim H0. AppE; [| exfalso0].
      apply ClaE in H1 as []. apply ClaE in H2 as []. tauto. }
    pose proof Huo as [[_ [_ [Hxu _]]] _].
    set (V := U - Derivaed ([x]) X cT).
    assert (Huv : V ⊂ U). { apply IncludP. intros z HZ... }
    assert (Hv : TONeigh x V X cT).
    { destruct Huo as [[_ [_ [_ [Z [Hz [Hxz Huz]]]]]] [_ Huo]].
      split. split... split... split. eapply ReSyTrP...
      exists (Z - Derivaed ([x]) X cT). split. eapply OpenClosedP...
      split. apply ClaI. tauto. eapply IncludP1...
      split. apply ClaI. split... eapply OpenClosedP... }
    pose proof Hv as Hv'. apply Hop, EmptyNE in Hv as [y Hv].
    apply ClaE in Hv as [Hyv Hyp]. apply ClaE in Hyv as [Hyu Hyd].
    apply ClaE in Hyp as [Hya Hxy].
    assert (Hnq : y ≠ x). { intro. elim Hxy. apply ClaI... }
    assert (Hw : ∃ W, W ∈ TNeighS y X cT /\ x ∉ W).
    { apply DerivaedP1 in Hyd as [W [Hw He]]... exists W. split.
      apply ClaI... apply LeTh3_6 in He... intro. assert (W ∩ [x] ≠ ∅).
      { apply EmptyNE. exists x. apply ClaI. split... apply SingI. }
      tauto. intros z Hz. apply SingE in Hz. subst... }
    destruct Hw as [W [Hw Hxw]].
    assert (Hv : V ∈ TNeighS y X cT).
    { apply ClaI. split... split... split. apply IncludP...
      exists (V - Derivaed ([x]) X cT). split.
      eapply OpenClosedP; try apply Hv'... split. apply ClaI. split...
      apply ClaI... apply IncludP. intros z Hz... } set (K:= W ∩ V).
    assert (Hk : K ∈ TNeighS y X cT). { apply Theorem3_4b... }
    apply ClaE in Hk. apply ClaE in Hya.
    apply Hya, EmptyNE in Hk as [z Hz].
    apply ClaE in Hz as [Hz Hzp]. apply ClaE in Hzp as [Hza Hzy].
    exists z. apply ClaI. assert (Hnq1 : z ≠ x).
    { apply ClaE in Hz as [Hz _]. intro. subst; tauto. }
    split. apply ClaE in Hz as []...
    apply ClaI. split... intro. apply ClaE in H. tauto.
Qed.