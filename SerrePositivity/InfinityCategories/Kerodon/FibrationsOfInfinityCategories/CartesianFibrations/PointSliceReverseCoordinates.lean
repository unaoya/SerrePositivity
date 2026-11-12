module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointSlicePrismReverse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointJoinReverseCoordinates

/-!
概要：頂点 slice の反転を、元の錐の射で全次数にわたり計算する。
方針：標準零単体の正規化と join の反転を分離する。
規約：元の錐とパラメーターをともに反転する。
使われ方：反転した輸送族と左 Hom の共通解像の照合。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 正規化済みの頂点 slice の反転は、join の反転と錐の後合成で表される。 -/
lemma cofinalPointSliceOverOpIso_app_val {B : SSet.{u}} (z : B _⦋0⦌)
    (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)).op _⦋n⦌) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso z).hom.left).app (Opposite.op ⦋n⦌) s).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋n⦌).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] Δ[0]).inv ≫
          SSet.opFunctor.map (SSet.opObjEquiv s).val := by
  let p := SSet.opFunctor.map (SSet.yonedaEquiv.symm z)
  let r := (stdSimplex.opIso.{u} ⦋0⦌).inv
  have he : r ≫ p = SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z) := by
    apply SSet.yonedaEquiv.injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseSimplex_yoneda, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change ((eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder he)).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p r).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso (SSet.yonedaEquiv.symm z)).hom.app _ s))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder_eqToHom_app_val he]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap r (𝟙 Δ[n]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpObjEquiv (SSet.yonedaEquiv.symm z) ⦋n⦌ s).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpObjEquiv_val, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.comp_id, Category.id_comp]
  rfl

/-- 右 pinched 単体を slice に移して反転すると、同じ反転単体の左点表示となる。 -/
lemma pointSliceReverseFiberIso_pinched_app_val {B : SSet.{u}} (x z : B _⦋0⦌)
    (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x z).op _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointSliceReverseFiberIso z x).hom.app (Opposite.op ⦋n⦌)
      ((SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToSliceFiber x z)).app _ s)).val.val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫ (stdSimplex.opIso ⦋n + 1⦌).inv ≫
        SSet.opFunctor.map (SSet.yonedaEquiv.symm (SSet.opObjEquiv s).val) := by
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso z).hom.left).app _
    (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedSimplexToFiber (SSet.opObjEquiv s)).val)).val = _
  rw [cofinalPointSliceOverOpIso_app_val]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] Δ[0]).inv ≫
    SSet.opFunctor.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
      SSet.yonedaEquiv.symm (SSet.opObjEquiv s).val) = _
  rw [Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ SSet.opFunctor.map (SSet.yonedaEquiv.symm (SSet.opObjEquiv s).val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointJoinReverseIso_inv_coordinates.{u} n)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
