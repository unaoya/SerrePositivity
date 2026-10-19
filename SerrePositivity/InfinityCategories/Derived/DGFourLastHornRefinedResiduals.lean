module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornRefinedData
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornCochainFiller
public import SerrePositivity.InfinityCategories.DGNerve.DataRhsComponents

/-! # 細分された実四次ホーンの二残差と最後辺

概要：新ホーンの R・K は元の同じ残差の閉前合成で、最後辺は元のまま。
方針：全回収データの一致と一般の rhs 輸送、未知 Q の零を使う。
規約：対象の等式輸送を異種等号で保持。使われ方：供給済み Q・A の新ホーンへの接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 実四次最後ホーンの最上位 rhs は、未知成分を除く既知残差 K そのもの。 -/
lemma dgFourLastHorn_rhs_top :
    (HornData.knownData σ).rhs Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) = dgFourLastHornTopResidual σ := by
  have hQ : (HornData.knownData σ).hom {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 :=
    dgFourLastHornKnownData_zero_unknown σ _ (by decide) _ _ _ _ _ _ _
  have ht := dgFourSimplex_rhs_top (HornData.knownData σ)
  rw [hQ, compose_zero, add_zero] at ht
  exact ht

variable (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 新しい実ホーンの欠面右辺は、元の R を同じ閉射で前合成したもの。 -/
lemma dgFourLastHornSourceRefinement_missingResidual :
    HEq (dgFourLastHornMissingResidual (dgFourLastHornSourceRefinement σ q s))
      (dgGradedPrecompose A D (-2 + 1) (dgFourLastHornMissingResidual σ) s) :=
  (SimplexData.rhs_heq_of_eq (dgFourLastHornSourceRefinement_knownData σ q s)
    {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide)).trans
      (dgSimplexDataInitialRefinement_rhs_from_zero A D (HornData.knownData σ) q s
        {0, 1, 2, 3} 3 (-2) (by decide) (by decide) (by decide) (by decide))

/-- 新しい実ホーンの既知残差 K も、元の K を同じ閉射で前合成したもの。 -/
lemma dgFourLastHornSourceRefinement_topResidual :
    HEq (dgFourLastHornTopResidual (dgFourLastHornSourceRefinement σ q s))
      (dgGradedPrecompose A D (-2) (dgFourLastHornTopResidual σ) s) := by
  have ht := congrArg (dgGradedPrecompose A D (-3 + 1) · s) (dgFourLastHorn_rhs_top σ)
  exact (heq_of_eq (dgFourLastHorn_rhs_top (dgFourLastHornSourceRefinement σ q s))).symm.trans
    ((SimplexData.rhs_heq_of_eq (dgFourLastHornSourceRefinement_knownData σ q s)
      Finset.univ 0 4 (-3) (by decide) (by decide) (by decide) (by decide)).trans
        ((dgSimplexDataInitialRefinement_rhs_from_zero A D (HornData.knownData σ) q s
          Finset.univ 4 (-3) (by decide) (by decide) (by decide) (by decide)).trans
            (heq_of_eq ht)))

/-- 新ホーンの最後の実斉次辺成分は、元の最後辺と同じ。 -/
lemma dgFourLastHornSourceRefinement_lastEdge :
    HEq ((HornData.knownData (dgFourLastHornSourceRefinement σ q s)).edgeHom 3 4 (by decide))
      ((HornData.knownData σ).edgeHom 3 4 (by decide)) :=
  (SimplexData.hom_heq_of_eq (dgFourLastHornSourceRefinement_knownData σ q s)
    {3, 4} 3 4 0 (by decide) (by decide) (by decide) (by decide)).trans
      (dgSimplexDataInitialRefinement_hom_ne_zero A D (HornData.knownData σ) q s
        {3, 4} 3 4 0 (by decide) (by decide) (by decide) (by decide) (by decide))

end SerrePositivity.InfinityCategories
