module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornRefinedData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornCochainFiller
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataRhsComponents

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 実四次最後ホーンの最上位 rhs は、未知成分を除く既知残差 K そのもの。 -/
lemma dgFourLastHorn_rhs_top :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).rhs Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ := by
  have hQ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).hom {0, 1, 2, 3} 0 3 (-2)
      (by decide) (by decide) (by decide) (by decide) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornKnownData_zero_unknown σ _ (by decide) _ _ _ _ _ _ _
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourSimplex_rhs_top (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
  rw [hQ, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, add_zero] at ht
  exact ht

variable (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))

/-- 新しい実ホーンの欠面右辺は、元の R を同じ閉射で前合成したもの。 -/
lemma dgFourLastHornSourceRefinement_missingResidual :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-2 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual σ) s) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_knownData σ q s)
    {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_rhs_from_zero A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s
        {0, 1, 2, 3} 3 (-2) (by decide) (by decide) (by decide) (by decide))

/-- 新しい実ホーンの既知残差 K も、元の K を同じ閉射で前合成したもの。 -/
lemma dgFourLastHornSourceRefinement_topResidual :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-2) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ) s) := by
  have ht := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-3 + 1) · s) (dgFourLastHorn_rhs_top σ)
  exact (heq_of_eq (dgFourLastHorn_rhs_top (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s))).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_knownData σ q s)
      Finset.univ 0 4 (-3) (by decide) (by decide) (by decide) (by decide)).trans
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_rhs_from_zero A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s
          Finset.univ 4 (-3) (by decide) (by decide) (by decide) (by decide)).trans
            (heq_of_eq ht)))

/-- 新ホーンの最後の実斉次辺成分は、元の最後辺と同じ。 -/
lemma dgFourLastHornSourceRefinement_lastEdge :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).edgeHom 3 4 (by decide))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_knownData σ q s)
    {3, 4} 3 4 0 (by decide) (by decide) (by decide) (by decide)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_hom_ne_zero A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s
        {3, 4} 3 4 0 (by decide) (by decide) (by decide) (by decide) (by decide))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
