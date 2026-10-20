module
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationHomotopy
public import SerrePositivity.InfinityCategories.Derived.PinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Derived.FunctorSliceEvaluationComponents

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
namespace SerrePositivity.InfinityCategories
/-- 実 slice 評価の任意の関手への制限は、同じ右 join prism の展開。 -/
lemma roofSliceEvaluationHomotopy_precomp_h {K X : SSet.{u}} (z : X _⦋0⦌)
    (a : K ⟶ sliceOver (SSet.yonedaEquiv.symm z)) :
    (functorHomotopyPrecomp (roofSliceEvaluationHomotopy z) a).h =
      (β_ K (Δ[1] : SSet.{u})).hom ≫ rightMappingSpacePrism K ≫ sliceOverUncurry a := by
  dsimp only [functorHomotopyPrecomp, roofSliceEvaluationHomotopy]
  have hb : (a ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (sliceOver (SSet.yonedaEquiv.symm z)) (Δ[1] : SSet.{u})).hom =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ a) := rfl
  rw [← Category.assoc, hb, Category.assoc, ← Category.assoc (Δ[1] ◁ a),
    rightMappingSpacePrism_naturality, Category.assoc, ← sliceOverUncurry_precomp,
    Category.comp_id]
/-- 実 pinched Hom 族の slice 表示を評価すると、同じ区間族の実円柱写像になる。 -/
lemma roofSliceEvaluationHomotopy_pinched_h {K X : SSet.{u}} {y z : X _⦋0⦌}
    (f : K ⟶ pinchedHom y z) :
    (functorHomotopyPrecomp (roofSliceEvaluationHomotopy z)
      (f ≫ pinchedFamilySlice X y z)).h =
        (intervalFamilyHomotopy (f ≫ pinchedHomToIntervalMappingSpace y z)).h := by
  rw [roofSliceEvaluationHomotopy_precomp_h]
  change _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
    intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace y z)
  rw [pinchedHomToIntervalMappingSpace_uncurry]
  rfl
/-- 実 pinched Hom 族上の普遍評価成分は、同じ族のパラメータ関手圏内の射。 -/
lemma roofFunctorSliceEvaluation_pinched_component_arrow {K X : SSet.{u}} {y z : X _⦋0⦌}
    (f : K ⟶ pinchedHom y z) :
    Arrow.mk ((homotopyNatTransOfEndpoints (roofFunctorSliceEvaluationHomotopy K z).h
      (roofFunctorSliceEvaluationHomotopy K z).h₀ (roofFunctorSliceEvaluationHomotopy K z).h₁).app
        (SSet.HomotopyCategory.mk (functorVertex (f ≫ pinchedFamilySlice X y z)))) =
      Arrow.mk (intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace y z)) := by
  let e₁ := functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp
    (roofSliceEvaluationHomotopy z) (f ≫ pinchedFamilySlice X y z))
  let e₂ := intervalFamilyEdge (f ≫ pinchedHomToIntervalMappingSpace y z)
  have he := congrArg (fun a : K ⊗ (Δ[1] : SSet.{u}) ⟶ X => SSet.yonedaEquiv (curry a))
    (roofSliceEvaluationHomotopy_pinched_h f)
  exact (roofFunctorSliceEvaluation_component_arrow K z (f ≫ pinchedFamilySlice X y z)).trans
    (Truncated.HomotopyCategory.congr_arrowMk_homMk e₁ e₂ he)
end SerrePositivity.InfinityCategories
