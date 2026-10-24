module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionSecondUnitSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTriangleFamily
/-!
概要：第二入力が閉恒等射である標準合成三角形全体の厳密退化を回収する。
方針：二時間の最大値による正方形を標準三角形へ制限する。
規約：Small 仮定を加えず、同じ coherent prism と元 Hom 入力を保持する。
使われ方：終側射影単位面の明示入力を除き、指定境界充填へ進む。
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
lemma dgGluingDGCompositionTriangleFamily_second_unit {K : SSet.{max u v}} {x y : E}
    (f : K ⟶ DGNerve.pinchedHom R E x y) :
    dgGluingDGCompositionTriangleFamily R E f
      (SSet.const (pinchedClosedVertex R E (𝟙 (ForgetEnrichment.of (Complex R) y)))) =
      (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingDGCompositionTriangleFamily, dgGluingSlicePrismTriangle_square_section,
    dgGluingDGCompositionSecondUnitSquare, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, dgGluingUnitSquareMax_section]
end SerrePositivity.InfinityCategories
