module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonInitialState

/-!
概要：元の二つの表示から、開始点を保持する初期全前置比較の存在を証明する。
方針：開始点の後への compact 因子化と、実三角形の全形状正規化を合成する。
規約：大域余極限の compact 性は仮定しない。使われ方：左右交互の再帰の初期値。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 指定開始点を保ち、右側ではその後から始まる、compact な初期全比較が存在する。 -/
lemma exists_comparisonInitialState {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
    [Quasicategory I₁] [IsKappaFiltered κ I₁]
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C)
    (c₀ : JoinCocone D₀) (c₁ : JoinCocone D₁) (hc₁ : IsColimitCone c₁)
    (hv : c₀.vertex = c₁.vertex) (a : I₀ _⦋0⦌) (b : I₁ _⦋0⦌)
    (ha : IsKappaCompact.{u, u + 1} κ (D₀.app _ (ULift.up a)))
    (hD₁ : ∀ j : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} κ (D₁.app _ (ULift.up j))) :
    ∃ s : CompactPresentationComparison κ D₀ D₁ c₀ c₁,
      s.left_index.app _ s.left_terminal = a ∧
      ∃ j : (sliceUnder (SSet.yonedaEquiv.symm b)) _⦋0⦌,
        s.right_index.app _ s.right_terminal =
          JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j := by
  obtain ⟨j, f, T, _⟩ := compactPresentations_initialTriangle D₀ D₁ c₀ c₁ hc₁ hv a b ha
  refine ⟨comparisonInitialState c₀ c₁ hv a
      (JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j) ha (hD₁ _) f T,
    ?_, j, ?_⟩
  · change (SSet.yonedaEquiv.symm a).app _ _ = a
    rw [SSet.yonedaEquiv_symm_zero]
    simp [SSet.const, SimplexCategory.const_eq_id]
  · change (SSet.yonedaEquiv.symm (JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j)).app _ _ = _
    rw [SSet.yonedaEquiv_symm_zero]
    simp [SSet.const, SimplexCategory.const_eq_id]

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
