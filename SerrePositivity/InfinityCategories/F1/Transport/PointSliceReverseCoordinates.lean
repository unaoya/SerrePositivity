module

public import SerrePositivity.InfinityCategories.F1.Joins.CoslicePostCoordinates
public import SerrePositivity.InfinityCategories.F1.Transport.PointSlicePrismReverse
public import SerrePositivity.InfinityCategories.F1.Transport.PointJoinReverseCoordinates

/-!
概要：頂点 slice の反転を、元の錐の射で全次数にわたり計算する。
方針：標準零単体の正規化と join の反転を分離する。
規約：元の錐とパラメーターをともに反転する。
使われ方：反転した輸送族と左 Hom の共通解像の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 正規化済みの頂点 slice の反転は、join の反転と錐の後合成で表される。 -/
lemma cofinalPointSliceOverOpIso_app_val {B : SSet.{u}} (z : B _⦋0⦌)
    (n : ℕ) (s : (sliceOver (SSet.yonedaEquiv.symm z)).op _⦋n⦌) :
    (((cofinalPointSliceOverOpIso z).hom.left).app (Opposite.op ⦋n⦌) s).val =
      joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋n⦌).inv ≫
        (stableJoinReverseIso Δ[n] Δ[0]).inv ≫
          SSet.opFunctor.map (SSet.opObjEquiv s).val := by
  let p := SSet.opFunctor.map (SSet.yonedaEquiv.symm z)
  let r := (stdSimplex.opIso.{u} ⦋0⦌).inv
  have he : r ≫ p = SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z) := by
    apply SSet.yonedaEquiv.injective
    rw [stableReverseSimplex_yoneda, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change ((eqToHom (congrArg sliceUnder he)).app (Opposite.op ⦋n⦌)
    ((sliceUnderRestrict p r).app _
      ((sliceOverOpIso (SSet.yonedaEquiv.symm z)).hom.app _ s))).val = _
  rw [sliceUnder_eqToHom_app_val he]
  change joinMap r (𝟙 Δ[n]) ≫
    (sliceOverOpObjEquiv (SSet.yonedaEquiv.symm z) ⦋n⦌ s).val = _
  rw [sliceOverOpObjEquiv_val, ← Category.assoc, ← joinMap_comp]
  simp only [Category.comp_id, Category.id_comp]
  rfl

/-- 右 pinched 単体を slice に移して反転すると、同じ反転単体の左点表示となる。 -/
lemma pointSliceReverseFiberIso_pinched_app_val {B : SSet.{u}} (x z : B _⦋0⦌)
    (n : ℕ) (s : (pinchedHom x z).op _⦋n⦌) :
    ((pointSliceReverseFiberIso z x).hom.app (Opposite.op ⦋n⦌)
      ((SSet.opFunctor.map (pinchedHomToSliceFiber x z)).app _ s)).val.val =
      (leftPointStdSimplexIso n).hom ≫ (stdSimplex.opIso ⦋n + 1⦌).inv ≫
        SSet.opFunctor.map (SSet.yonedaEquiv.symm (SSet.opObjEquiv s).val) := by
  change (((cofinalPointSliceOverOpIso z).hom.left).app _
    (SSet.opObjEquiv.symm (pinchedSimplexToFiber (SSet.opObjEquiv s)).val)).val = _
  rw [cofinalPointSliceOverOpIso_app_val]
  change joinMap _ _ ≫ (stableJoinReverseIso Δ[n] Δ[0]).inv ≫
    SSet.opFunctor.map ((joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (SSet.opObjEquiv s).val) = _
  rw [Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ SSet.opFunctor.map (SSet.yonedaEquiv.symm (SSet.opObjEquiv s).val))
    (pointJoinReverseIso_inv_coordinates.{u} n)

end SerrePositivity.InfinityCategories
