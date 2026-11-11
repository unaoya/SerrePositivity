module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedRoofHomInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofFunctor
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.PinchedSliceTransport
/-!
概要：閉分母上の実係数族の任意標的での屋根像について、両射影を厳密に計算する。
方針：閉 fiber 包含と slice の後合成の全次元の可換性を合成する。
規約：元の閉始域を保つ。使われ方：実評価ホモトピーの両端の照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
/-- 閉分母上の係数の任意標的への屋根像は、係数の像そのものを実 slice 成分に持つ。 -/
lemma dgClosedRoofImage_target (P : Set D) (x y : D)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F) ≫
      pullback.fst _ _ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) r.obj.left))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice Y
        (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) r.obj.left)))
        (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_target, ← Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y) ≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_target]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_pinched F _ _
/-- 閉分母上の係数の屋根像は、元の実閉分母の上にある。 -/
lemma dgClosedRoofImage_projection (P : Set D) (x y : D)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F
        (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x r) := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_projection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_projection]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
