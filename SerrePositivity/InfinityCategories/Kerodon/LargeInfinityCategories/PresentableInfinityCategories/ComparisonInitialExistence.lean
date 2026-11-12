module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonInitialState

/-!
概要：元の二つの表示から、開始点を保持する初期全前置比較の存在を証明する。
方針：開始点の後への compact 因子化と、実三角形の全形状正規化を合成する。
規約：大域余極限の compact 性は仮定しない。使われ方：左右交互の再帰の初期値。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 指定開始点を保ち、右側ではその後から始まる、compact な初期全比較が存在する。 -/
lemma exists_comparisonInitialState {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
    [Quasicategory I₁] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I₁]
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C)
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
    (hv : c₀.vertex = c₁.vertex) (a : I₀ _⦋0⦌) (b : I₁ _⦋0⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D₀.app _ (ULift.up a)))
    (hD₁ : ∀ j : I₁ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D₁.app _ (ULift.up j))) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison κ D₀ D₁ c₀ c₁,
      s.left_index.app _ s.left_terminal = a ∧
      ∃ j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm b)) _⦋0⦌,
        s.right_index.app _ s.right_terminal =
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j := by
  obtain ⟨j, f, T, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactPresentations_initialTriangle D₀ D₁ c₀ c₁ hc₁ hv a b ha
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonInitialState c₀ c₁ hv a
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j) ha (hD₁ _) f T,
    ?_, j, ?_⟩
  · change (SSet.yonedaEquiv.symm a).app _ _ = a
    rw [SSet.yonedaEquiv_symm_zero]
    simp [SSet.const, SimplexCategory.const_eq_id]
  · change (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j)).app _ _ = _
    rw [SSet.yonedaEquiv_symm_zero]
    simp [SSet.const, SimplexCategory.const_eq_id]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
