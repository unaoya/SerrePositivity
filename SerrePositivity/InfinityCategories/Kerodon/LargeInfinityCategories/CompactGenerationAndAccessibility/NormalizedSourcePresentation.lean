module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ConeSourceForget

/-!
概要：指定終点を固定した自明 Kan 持ち上げから、元の入力図式の下の全表示を回収する。
方針：全余錐を持ち上げ、固定余錐の忘却の filtered 保存性を使う。
規約：指定された全余錐と元の終点を厳密に保つ。
使われ方：元の compact 成分表示の入力付き正規化。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：自明 Kan 射に沿う指定終点付き全表示を元の入力図式の下へ戻す。
方針：同じ全余錐を持ち上げ、全同値で余極限性を反映して固定余錐を忘却する。
規約：元の最終頂点と各表示段の底を厳密に保持する。
使われ方：元の成分表示の入力付き正規化。 -/
lemma exists_normalizedSourcePresentation
    {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {K C T : SSet.{u + 1}} [Quasicategory C] [Quasicategory T]
    {q : K ⟶ C} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder w.val ⟶ T) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration r]
    (ρ : T ⟶ C) (hr : r ≫ ρ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection w.val)
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ T)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder w.val) _⦋0⦌) (ht : r.app (Opposite.op ⦋0⦌) t = c.vertex) :
    ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q,
      F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q = D ≫ ρ ∧
      ∃ c' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c' ∧
        c'.vertex = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.coneSourceForget w).app (Opposite.op ⦋0⦌) t ∧
        c'.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q = c.val ≫ ρ := by
  obtain ⟨L, d, hd, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_cocone_lift_with_vertex r c t ht
  have hL : L ≫ r = D := by
    have h := congrArg (fun F ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj I) Δ[0] ≫ F) hd
    rw [← Category.assoc, d.property, c.property] at h
    exact h
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration r) d).mpr
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ hd).mpr hc)
  refine ⟨L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.coneSourceForget w, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.coneSourceForget w) d,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.coneSourceForget_isKappaAccessibleFunctor hμ w I L d hd', ?_, ?_⟩
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.coneSourceForget_projection, ← hr, ← Category.assoc, hL]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, hv]
  · change (d.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.coneSourceForget w) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q = c.val ≫ ρ
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.coneSourceForget_projection, ← hr, ← Category.assoc, hd]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
