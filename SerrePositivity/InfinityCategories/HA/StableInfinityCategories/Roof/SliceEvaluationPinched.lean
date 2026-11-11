module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.SliceEvaluationHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.PinchedFamilyComposition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.FunctorSliceEvaluationComponents

/-!
概要：普遍 slice 評価を実 pinched Hom 族へ制限し、同じ区間表示と射の類を回収する。
方針：右 join prism と全パラメータ制限の厳密な自然性を使う。
規約：同じ円柱上の実写像を保持する。使われ方：実屋根表示の値の高次パラメータ比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof
/-- 実 slice 評価の任意の関手への制限は、同じ右 join prism の展開。 -/
lemma roofSliceEvaluationHomotopy_precomp_h {K X : SSet.{u}} (z : X _⦋0⦌)
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) a).h =
      (β_ K (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy]
  have hb : (a ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) (Δ[1] : SSet.{u})).hom =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ a) := rfl
  rw [← Category.assoc, hb, Category.assoc, ← Category.assoc (Δ[1] ◁ a),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_naturality, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp,
    Category.comp_id]
/-- 実 pinched Hom 族の slice 表示を評価すると、同じ区間族の実円柱写像になる。 -/
lemma roofSliceEvaluationHomotopy_pinched_h {K X : SSet.{u}} {y z : X _⦋0⦌}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y z) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z)
      (f ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X y z)).h =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace y z)).h := by
  rw [roofSliceEvaluationHomotopy_precomp_h]
  change _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace y z)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry]
  rfl
/-- 実 pinched Hom 族上の普遍評価成分は、同じ族のパラメータ関手圏内の射。 -/
lemma roofFunctorSliceEvaluation_pinched_component_arrow {K X : SSet.{u}} {y z : X _⦋0⦌}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y z) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z).h₁).app
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X y z)))) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace y z)) := by
  let e₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) (f ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X y z))
  let e₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace y z)
  have he := congrArg (fun a : K ⊗ (Δ[1] : SSet.{u}) ⟶ X => SSet.yonedaEquiv (curry a))
    (roofSliceEvaluationHomotopy_pinched_h f)
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluation_component_arrow K z (f ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X y z)).trans
    (Truncated.HomotopyCategory.congr_arrowMk_homMk e₁ e₂ he)
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof
