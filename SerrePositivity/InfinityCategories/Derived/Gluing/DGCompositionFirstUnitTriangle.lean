module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTriangleFamily
public import SerrePositivity.InfinityCategories.Derived.Gluing.SlicePrismUnitGeometry
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionUnitLaws
/-!
概要：第一入力が閉恒等射である標準合成三角形全体の退化を回収する。
方針：D の全パラメーター単位則を一定位相の slice prism の三角形化へ適用する。
規約：Small 仮定を加えず、元の coherent prism と全入力を保持する。
使われ方：前正規化の始側単位面を同じ二単体族の厳密退化として消去する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

lemma dgGluingDGCompositionTriangleFamily_first_unit {K : SSet.{max u v}} {x y : E}
    (g : K ⟶ DGNerve.pinchedHom R E x y) :
    dgGluingDGCompositionTriangleFamily R E
      (SSet.const (pinchedClosedVertex R E (𝟙 (ForgetEnrichment.of (Complex R) x)))) g =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫
        intervalMappingUncurry (g ≫ pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingDGCompositionTriangleFamily, dgPinchedCompositionFamilyPrism_first_unit,
    dgGluingSlicePrismTriangle_constant]
  simpa only [pinchedHomUncurry, dgPinchedHomSlice, Category.assoc] using
    congrArg (fun k => (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ k)
      (pinchedHomToIntervalMappingSpace_uncurry g).symm
end SerrePositivity.InfinityCategories
