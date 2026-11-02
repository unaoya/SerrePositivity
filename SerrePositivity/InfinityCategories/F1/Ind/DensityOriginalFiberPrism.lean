module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.ElementsDiagram
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.HomotopyTransformationVertex
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityCocone
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityDiagramHomotopy
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.Ind.ConstantIntervalTranspose
public import SerrePositivity.InfinityCategories.F1.Ind.ConstantIntervalTransposePrism
public import SerrePositivity.InfinityCategories.F1.Ind.DensityFiberTransformationFamily
public import SerrePositivity.InfinityCategories.F1B.Ind.DensityFiberTransformationRestriction
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceInterval

/-!
概要：元の大域密度変換の fiber 作用から、同じ全円柱を厳密に回収する。
方針：定値図式間の転置の往復を、同じ fiber への制限に適用する。
規約：選択した元の密度変換と全 fiber パラメータを保つ。
使われ方：元の共同 Hom の unstraightening の値写像への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "A" => presheafDensityFiberParameter F x
local notation "E" => presheafDensityElementsParameter F
local notation "i" => presheafDensityFiberParameterInclusion F x

/-- 元の大域変換の fiber 作用の円柱は、同じ元の密度円柱を制限したもの。 -/
lemma presheafDensityOriginalFiberInterval_prism :
    intervalMappingUncurry (presheafDensityOriginalFiberInterval F x) =
      (Δ[1] ◁ i) ≫ (β_ Δ[1] E).hom ≫ (presheafDensityDiagramHomotopy F).h := by
  have h := constantIntervalTranspose_uncurry A (PresheafInfinity C)
    (functorVertex (representablePresheafInfinity x)) (functorVertex F)
    ((densityFiberTransformationRestriction F x).app (Opposite.op ⦋0⦌)
      (presheafDensityTransformationVertex F))
  change intervalMappingUncurry (presheafDensityOriginalFiberInterval F x) = _ at h
  rw [densityFiberTransformationRestriction_vertex, homotopyTransformationVertex_h] at h
  rw [h]
  change (β_ Δ[1] A).hom ≫ (i ▷ Δ[1]) ≫
    (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex
      (presheafDensityTransformationVertex F)).toTruncated).h = _
  rw [presheafDensityTransformationVertex, homotopyTransformationVertex_h]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
