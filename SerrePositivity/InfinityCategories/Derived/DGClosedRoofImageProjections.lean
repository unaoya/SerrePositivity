module
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofHomInclusion
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoofFunctor
public import SerrePositivity.InfinityCategories.Derived.PinchedSliceTransport
/-!
概要：閉分母上の実係数族の任意標的での屋根像について、両射影を厳密に計算する。
方針：閉 fiber 包含と slice の後合成の全次元の可換性を合成する。
規約：元の閉始域を保つ。使われ方：実評価ホモトピーの両端の照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
/-- 閉分母上の係数の任意標的への屋根像は、係数の像そのものを実 slice 成分に持つ。 -/
lemma dgClosedRoofImage_target (P : Set D) (x y : D)
    (r : DGClosedVerdierDenominators A D P x)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) :
    (dgClosedRoofHomInclusion A D P x y r ≫ dgInvertingRoofFunctorMap A D P x y F) ≫
      pullback.fst _ _ =
    pinchedHomMap F (Simplex.vertex (ForgetEnrichment.to (Complex A) r.obj.left))
      (Simplex.vertex y) ≫ pinchedFamilySlice Y
        (F.app (Opposite.op ⦋0⦌) (Simplex.vertex (ForgetEnrichment.to (Complex A) r.obj.left)))
        (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) := by
  rw [Category.assoc, dgInvertingRoofFunctorMap_target, ← Category.assoc]
  change (dgClosedRoofHomInclusion A D P x y r ≫ dgRoofCorrespondenceTarget A D P x y) ≫
    roofTargetSliceMap F (Simplex.vertex y) = _
  rw [dgClosedRoofHomInclusion_target]
  exact roofTargetSliceMap_pinched F _ _
/-- 閉分母上の係数の屋根像は、元の実閉分母の上にある。 -/
lemma dgClosedRoofImage_projection (P : Set D) (x y : D)
    (r : DGClosedVerdierDenominators A D P x)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) :
    (dgClosedRoofHomInclusion A D P x y r ≫ dgInvertingRoofFunctorMap A D P x y F) ≫
      dgInvertingRoofProjection A D P x F
        (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) =
      SSet.const (dgClosedVerdierDenominatorVertex A D P x r) := by
  rw [Category.assoc, dgInvertingRoofFunctorMap_projection, dgClosedRoofHomInclusion_projection]
end SerrePositivity.InfinityCategories
