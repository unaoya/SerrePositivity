module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionSecondUnitSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionTriangleFamily
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
lemma dgGluingDGCompositionTriangleFamily_second_unit {K : SSet.{max u v}} {x y : E}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R E f
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R E (𝟙 (ForgetEnrichment.of (Complex R) y)))) =
      (stdSimplex.σ (1 : Fin 2) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_square_section,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionSecondUnitSquare, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSquareMax_section]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
