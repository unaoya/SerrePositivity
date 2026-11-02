module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberPullback
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.Ind.VertexFiberIsoProjection
public import SerrePositivity.InfinityCategories.F1.Ind.YonedaSlice
public import SerrePositivity.InfinityCategories.F1.Ind.YonedaSliceFiber
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
概要：Yoneda comma の fiber と写像空間の同型が、元の slice 全空間への射影を保つこと。
方針：引き戻し fiber、頂点の等式、pinched fiber 同型の同じ合成を計算する。
規約：同型の順方向を明示し、同値な別の写像へ置き換えない。
使われ方：元の元の圏から Yoneda comma への大域比較の実際の fiber 作用。
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

/-- 元の写像空間同型を slice に戻すと、元の Yoneda comma の射影そのもの。 -/
lemma presheafYonedaSliceFiberMappingIso_projection :
    (presheafYonedaSliceFiberMappingIso F x).hom ≫
      (pinchedHomSliceFiberIso (functorVertex (representablePresheafInfinity x))
        (functorVertex F)).hom ≫
      vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F)))
        (functorVertex (representablePresheafInfinity x)) =
    vertexFiberι (presheafYonedaSliceProjection F) (ULift.up x) ≫
      pullback.fst (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F)))
        (yonedaInfinityMap C) := by
  simp only [presheafYonedaSliceFiberMappingIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [vertexFiber_vertexEqToIso_ι _ (yonedaInfinityMap_vertex x)]
  exact vertexFiberPullbackIso_hom_ι _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
