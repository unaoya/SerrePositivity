module

public import SerrePositivity.InfinityCategories.F2.Ind.PointSliceComparison

/-!
概要：同じ slice 比較の全 fiber 作用は、元の関手の pinched Hom 作用そのもの。
方針：引き戻しと fiber の包含後で uncurry し、同じ全錐の後合成を照合する。
規約：全 fiber パラメータ上の厳密な等式。
使われ方：充満忠実性から元の slice 比較の全空間の同値性を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C D : SSet.{u}} (f : C ⟶ D) (x y : C _⦋0⦌)
local notation "p" => sliceOverProjection (SSet.yonedaEquiv.symm y)
local notation "q" => pointSlicePullbackProjection f y
local notation "t" => sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y))

/-- 元の同じ fiber 作用は、両側の標準同型の下で元の pinched Hom 作用そのもの。 -/
lemma pointSliceComparison_fiber_hom :
    (pinchedHomSliceFiberIso x y).hom ≫
      vertexFiberMap p q (pointSliceComparison f y) (pointSliceComparison_projection f y) x ≫
      (vertexFiberPullbackIso t f x).hom =
    pinchedHomMap f x y ≫
      (pinchedHomSliceFiberIso (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)).hom := by
  apply vertexFiber_hom_ext t (f.app (Opposite.op ⦋0⦌) x)
  simp only [Category.assoc, vertexFiberPullbackIso_hom_ι, pointSlicePullbackProjection]
  rw [← Category.assoc (vertexFiberMap p (pullback.snd t f) _ _ x), vertexFiberMap_ι]
  simp only [Category.assoc, pointSliceComparison, pullback.lift_fst]
  apply sliceOverUncurry_injective
  change sliceOverUncurry (((pinchedHomSliceFiberIso x y).hom ≫ vertexFiberι p x) ≫
    pointSlicePostcomp f y) = pinchedHomUncurry (pinchedHomMap f x y)
  rw [pointSlicePostcomp_uncurry]
  have h := pinchedHomUncurry_postcomp (𝟙 (pinchedHom x y)) f
  simpa only [pinchedHomUncurry, Category.id_comp] using h.symm

end SerrePositivity.InfinityCategories.F2.Ind
