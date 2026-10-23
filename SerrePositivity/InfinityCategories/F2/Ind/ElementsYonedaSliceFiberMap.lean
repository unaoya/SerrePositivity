module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaSliceFiberProjection
public import SerrePositivity.InfinityCategories.F2.Ind.ElementsYonedaSliceComparison
public import SerrePositivity.InfinityCategories.F1.Universe.Fiber

/-!
概要：構成済みの元の大域比較そのものの fiber 作用を、元の前層写像空間への射として固定する。
方針：同じ底上の比較を fiber に制限し、宇宙同型と元の Yoneda comma の fiber 同型を合成する。
規約：元の全空間への包含後に、元の密度 slice 射を厳密に回収する。
使われ方：Yoneda comma の小さいモデルの同値性の検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F

/-- 元の大域比較の、持ち上げた元の指定 fiber 上での同じ作用。 -/
def presheafElementsYonedaSliceFiberMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (vertexFiber p x) ⟶
      vertexFiber (presheafYonedaSliceProjection F) (ULift.up x) :=
  (uliftVertexFiberIso.{u, u + 1} p x).hom ≫
    vertexFiberMap ((SSet.uliftFunctor.{u + 1, u}).map p)
      (presheafYonedaSliceProjection F) (presheafElementsYonedaSliceComparison F)
      (presheafElementsYonedaSliceComparison_projection F) (ULift.up x)

/-- 元の Yoneda 写像空間への同じ fiber 作用。 -/
def presheafElementsYonedaSliceMapping :
    (SSet.uliftFunctor.{u + 1, u}).obj (vertexFiber p x) ⟶
      pinchedHom (functorVertex (representablePresheafInfinity x)) (functorVertex F) :=
  presheafElementsYonedaSliceFiberMap F x ≫ (presheafYonedaSliceFiberMappingIso F x).hom

/-- 同じ fiber 作用を slice へ含めると、元の密度 slice 射そのものを回収する。 -/
lemma presheafElementsYonedaSliceMapping_projection :
    presheafElementsYonedaSliceMapping F x ≫
      (pinchedHomSliceFiberIso (functorVertex (representablePresheafInfinity x))
        (functorVertex F)).hom ≫
      vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F)))
        (functorVertex (representablePresheafInfinity x)) =
    (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι p x) ≫ presheafDensitySliceMap F := by
  rw [presheafElementsYonedaSliceMapping, Category.assoc,
    presheafYonedaSliceFiberMappingIso_projection, presheafElementsYonedaSliceFiberMap]
  have h := vertexFiberMap_ι ((SSet.uliftFunctor.{u + 1, u}).map p)
    (presheafYonedaSliceProjection F) (presheafElementsYonedaSliceComparison F)
    (presheafElementsYonedaSliceComparison_projection F) (ULift.up x)
  calc
    _ = (uliftVertexFiberIso.{u, u + 1} p x).hom ≫
        vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map p) (ULift.up x) ≫
          presheafElementsYonedaSliceComparison F ≫ pullback.fst _ _ := by
      simpa only [Category.assoc] using (congrArg (fun t => (uliftVertexFiberIso.{u, u + 1} p x).hom ≫
        t ≫ pullback.fst _ _) h)
    _ = _ := by
      rw [← Category.assoc (uliftVertexFiberIso.{u, u + 1} p x).hom,
        uliftVertexFiberIso_hom_ι]
      congr 1
      exact pullback.lift_fst _ _ _

/-- 元の fiber 作用が表す全余錐は、元の密度余錐を同じ fiber へ制限したものそのもの。 -/
lemma presheafElementsYonedaSliceMapping_uncurry :
    sliceOverUncurry (presheafElementsYonedaSliceMapping F x ≫
      (pinchedHomSliceFiberIso (functorVertex (representablePresheafInfinity x))
        (functorVertex F)).hom ≫
      vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F)))
        (functorVertex (representablePresheafInfinity x))) =
    joinMap ((SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι p x)) (𝟙 Δ[0]) ≫
      (presheafDensityCocone F).val := by
  rw [presheafElementsYonedaSliceMapping_projection, sliceOverUncurry_precomp,
    presheafDensitySliceMap, sliceOverUncurry_curry]

end SerrePositivity.InfinityCategories.F2.Ind
