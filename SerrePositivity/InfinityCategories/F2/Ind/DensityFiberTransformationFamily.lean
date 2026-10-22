module

public import SerrePositivity.InfinityCategories.F2.Ind.DensityFiberTransformationRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.ConstantIntervalTranspose

/-!
概要：密度変換空間を、元の fiber 上の区間写像の全パラメータ族へ移す。
方針：同じ fiber への制限と定値図式間の変換の転置を合成する。
規約：native 余錐の指定頂点で、元の Yoneda comma の作用を厳密に回収する。
使われ方：native 変換と元の大域変換との同型を、同じ fiber の写像へ移す。
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
local notation "T" => intervalMappingSpace (functorVertex (presheafElementsYonedaDiagram F))
  (functorVertex (SSet.const (functorVertex F) : E ⟶ PresheafInfinity C))

/-- 元の全密度変換を、同じ fiber 上の区間写像の全族へ移す。 -/
def densityFiberTransformationFamily : T ⟶ (ihom A).obj
    (intervalMappingSpace (functorVertex (representablePresheafInfinity x)) (functorVertex F)) :=
  densityFiberTransformationRestriction F x ≫ constantIntervalTranspose A (PresheafInfinity C)
    (functorVertex (representablePresheafInfinity x)) (functorVertex F)

/-- native 密度変換の族は、元の Yoneda comma の同じ区間作用そのもの。 -/
lemma densityFiberTransformationFamily_native :
    (densityFiberTransformationFamily F x).app (Opposite.op ⦋0⦌)
      (presheafDensityCoconeTransformationVertex F) =
        functorVertex (presheafElementsYonedaSliceInterval F x) := by
  refine constantIntervalTranspose_vertex A (PresheafInfinity C)
    (functorVertex (representablePresheafInfinity x)) (functorVertex F)
    ((densityFiberTransformationRestriction F x).app (Opposite.op ⦋0⦌)
      (presheafDensityCoconeTransformationVertex F))
    (presheafElementsYonedaSliceInterval F x) ?_
  rw [densityFiberTransformationRestriction_vertex, homotopyTransformationVertex_h]
  calc
    _ = (Δ[1] ◁ i) ≫ (β_ Δ[1] E).hom ≫
        (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex
          (presheafDensityCoconeTransformationVertex F)).toTruncated).h :=
      presheafElementsYonedaSliceInterval_prism F x
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      rfl

/-- 元の大域変換が同じ fiber 上に定める区間作用。 -/
def presheafDensityOriginalFiberInterval : A ⟶
    intervalMappingSpace (functorVertex (representablePresheafInfinity x)) (functorVertex F) :=
  (functorVertexEquiv A _).symm ((densityFiberTransformationFamily F x).app
    (Opposite.op ⦋0⦌) (presheafDensityTransformationVertex F))

/-- 元の comma の作用と元の大域変換の作用を、同じ全 fiber 上で比較する。 -/
def presheafDensityFiberIntervalIso :
    FunctorIso (presheafElementsYonedaSliceInterval F x)
      (presheafDensityOriginalFiberInterval F x) := by
  have h := VertexIso.map (presheafDensityCoconeTransformationIso F)
    (densityFiberTransformationFamily F x)
  rw [densityFiberTransformationFamily_native] at h
  exact h ≪≫ eqToIso (congrArg HomotopyCategory.mk
    ((functorVertexEquiv A _).apply_symm_apply _).symm)

end SerrePositivity.InfinityCategories.F2.Ind
