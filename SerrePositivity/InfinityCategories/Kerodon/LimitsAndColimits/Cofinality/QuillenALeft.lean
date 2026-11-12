module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenASliceOpposite
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：left cofinality を弱可縮な slice の引き戻しで特徴付ける Quillen A。
方針：right 側の定理を反転し、底上の slice の同型と弱可縮性の反転判定で戻す。
規約：標的だけが quasicategory、始域と引き戻した slice の Kan 性は不要。
使われ方：Kerodon Theorem 7.2.3.1(1)（Tag 02NY）、HTT Theorem 4.1.3.1 の双対、A2h の始対象の場合。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：left cofinality は各 slice 引き戻しの弱可縮性と同値。
方針：反転した射への right 側の Quillen A と頂点の反転の全単射を使う。
規約：標的 B のみ quasicategory、始域 A は任意の単体集合。
使われ方：Kerodon Theorem 7.2.3.1(1)（Tag 02NY）、極限を計算する向きの cofinality 判定。 -/
@[kerodon 02NY]
lemma isLeftCofinal_iff_weaklyContractible_slices {A B : SSet.{u}} [Quasicategory B]
    (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f ↔ ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_isRightCofinal_op, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_weaklyContractible_coslices]
  constructor
  · intro h b
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalWeaklyContractible_slice_iff_op_coslice f b).mpr (h (SSet.opObjEquiv.symm b))
  · intro h b
    have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalWeaklyContractible_slice_iff_op_coslice f (SSet.opObjEquiv b)).mp
      (h (SSet.opObjEquiv b))
    exact hb

/-- 概要：全ての slice 引き戻しが弱可縮なら射は left cofinal。
方針：left 側の Quillen A の判定を使う。
規約：元の始域の quasicategory 性は不要。
使われ方：始対象の包含や点ごとの Kan 拡張の形状の判定。 -/
lemma isLeftCofinal_of_weaklyContractible_slices {A B : SSet.{u}} [Quasicategory B]
    (f : A ⟶ B)
    (hc : ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f := (isLeftCofinal_iff_weaklyContractible_slices f).mpr hc

/-- 概要：left cofinal な射の各 slice 引き戻しは弱可縮。
方針：left 側の Quillen A の必要性に特殊化する。
規約：弱可縮性のみを主張する。
使われ方：A2h の始対象の場合を同じ判定で回収する。 -/
lemma IsLeftCofinal.slice_isWeaklyContractible {A B : SSet.{u}} [Quasicategory B]
    {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))) :=
  (isLeftCofinal_iff_weaklyContractible_slices f).mp hf b

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
