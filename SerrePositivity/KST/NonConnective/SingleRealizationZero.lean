module

public import SerrePositivity.KST.NonConnective.BoundaryAdditivity
public import SerrePositivity.KST.SConstruction.ObjectSConstantRestriction

/-!
概要：零完全関手の一重 S• 実現への作用を、元の零図式で計算する。
方針：core と gapped の包含後で定値後合成を計算する。
規約：同じ零対象を保持する。使われ方：加法性の二つの標準軸。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

/-- 零完全関手の一重実現は、同じ零対象の零図式への定値写像。 -/
lemma singleRealization_constantZero (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X.carrier) :
    (multiRealizationFunctor 1).map (stableConstantZero X z) =
      SSet.const (Y := (multiRealizationFunctor 1).obj X)
        (coreSConstructionZeroVertex 0 z.vertex z.isZero) := by
  ext n a
  apply Subtype.ext
  apply Subtype.ext
  apply SSet.yonedaEquiv.symm.injective
  apply (ihom.adjunction (arNerve n.unop.len)).homEquiv _ _ |>.symm.injective
  ext d b
  rfl

/-- 同じ零関手は一重実現の全零境界商上で厳密に零射となる。 -/
lemma singleBoundary_constantZero (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X.carrier) :
    boundaryReducedRealizationMap 0 (stableConstantZero X z) = 0 := by
  apply PointedObject.cofiber_hom_ext (zeroDirectionsFatBoundary 1 X).ι
  change boundaryReductionQuotient 0 X ≫
      (boundaryReducedRealizationMap 0 (stableConstantZero X z)).right =
    boundaryReductionQuotient 0 X ≫
      (0 : boundaryReducedRealization 0 X ⟶ boundaryReducedRealization 0 X).right
  rw [boundaryReducedRealizationMap_quotient, singleRealization_constantZero]
  have h := Under.w (boundaryReductionPointedMap 0 X
    (coreSConstructionZeroVertex 0 z.vertex z.isZero))
  change SSet.const (Y := (multiRealizationFunctor 1).obj X)
      (coreSConstructionZeroVertex 0 z.vertex z.isZero) ≫
        boundaryReductionQuotient 0 X = (boundaryReducedRealization 0 X).hom at h
  have hc := congrArg (fun f ↦
    CategoryTheory.CartesianMonoidalCategory.toUnit ((multiRealizationFunctor 1).obj X) ≫ f) h
  rw [← Category.assoc, SSet.comp_const] at hc
  simpa only [PointedObject.zero_right, multiDiagonalCoreSConstruction,
    CategoryTheory.CartesianMonoidalCategory.comp_toUnit_assoc] using hc

end SerrePositivity.KST.NonConnective
