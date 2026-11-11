module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionTriangleFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SlicePrismUnitGeometry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedCompositionUnitLaws
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingDGCompositionTriangleFamily_first_unit {K : SSet.{max u v}} {x y : E}
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R E
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R E (𝟙 (ForgetEnrichment.of (Complex R) x)))) g =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_first_unit,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_constant]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice, Category.assoc] using
    congrArg (fun k => (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry g).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
