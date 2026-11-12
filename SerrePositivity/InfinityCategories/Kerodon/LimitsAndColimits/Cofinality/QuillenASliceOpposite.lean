module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.WeakContractibleOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRestrictionIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceTriangleFiber
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：頂点での slice の引き戻しの反転を、反転した頂点での coslice の引き戻しへ移す。
方針：sliceOverOpIso を標準零単体の反転同型による制限で正規化する。
規約：射影との可換性を通常の Over 圏の同型として保持する。
使われ方：Quillen A の left 側の弱可縮条件を right 側へ移す。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：頂点下の slice の反転は、反転した頂点からの coslice と底上で同型。
方針：一般の slice 反転同型の固定図式を、標準零単体の反転同型で正規化する。
規約：点の定義域 Δ[0].op と Δ[0] を定義的に同一視しない。
使われ方：引き戻し全体の反転の同型の構成。 -/
def cofinalPointSliceOverOpIso {B : SSet.{u}} (b : B _⦋0⦌) :
    Over.mk (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))) ≅
      Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm b))) := by
  let p := SSet.opFunctor.map (SSet.yonedaEquiv.symm b)
  let r := (stdSimplex.opIso.{u} ⦋0⦌).inv
  have he : r ≫ p = SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm b) := by
    apply SSet.yonedaEquiv.injective
    change SSet.yonedaEquiv ((stdSimplex.opIso.{u} ⦋0⦌).inv ≫
      SSet.opFunctor.map (SSet.yonedaEquiv.symm b)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseSimplex_yoneda, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let e₀ : Over.mk (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))) ≅
      Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) :=
    Over.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso (SSet.yonedaEquiv.symm b))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso_projection (SSet.yonedaEquiv.symm b))
  let e₁ : Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) ≅ Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ p)) :=
    Over.isoMk (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p r)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p r)
  exact e₀ ≪≫ e₁ ≪≫ eqToIso (congrArg (fun q ↦ Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q)) he)

/-- 概要：slice への引き戻しの反転は反転した頂点の coslice への引き戻しと同型。
方針：反転の pullback 保存と、底上の slice の同型による pullback の射を合成する。
規約：元の射と元の二対象に充填性は要求しない。
使われ方：left 側の Quillen A の弱可縮性の条件の移送。 -/
def cofinalSlicePullbackOpIso {A B : SSet.{u}} (f : A ⟶ B) (b : B _⦋0⦌) :
    (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))).op ≅
      pullback (SSet.opFunctor.map f)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm b))) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  let e := cofinalPointSliceOverOpIso b
  let m := pullback.map (SSet.opFunctor.map f)
    (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b)))
    (SSet.opFunctor.map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm b)))
    (𝟙 A.op) e.hom.left (𝟙 B.op) (by simp) (by simpa using e.hom.w.symm)
  exact PreservesPullback.iso SSet.opFunctor f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b)) ≪≫
    asIso m

/-- 概要：slice 引き戻しの弱可縮性と反転後の coslice 引き戻しの弱可縮性は同値。
方針：一般の弱可縮性の反転判定と引き戻し同型を合成する。
規約：引き戻しの Kan 性は不要。
使われ方：right 側の Quillen A の条件を left 側へ書き換える。 -/
lemma cofinalWeaklyContractible_slice_iff_op_coslice {A B : SSet.{u}} (f : A ⟶ B)
    (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback (SSet.opFunctor.map f)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm b)))) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (cofinalSlicePullbackOpIso f b).hom
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.isWeaklyContractible_op_iff _).symm.trans
    hi.isWeakHomotopyEquivalence.weaklyContractible_iff

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
