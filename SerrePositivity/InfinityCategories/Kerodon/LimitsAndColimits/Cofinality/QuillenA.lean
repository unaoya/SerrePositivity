module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenARightFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：right cofinality を弱可縮な coslice の引き戻しで特徴付ける Quillen A。
方針：right anodyne・right fibration 因子分解で始域を置き換え、弱可縮な Kan fiber で判定する。
規約：標的だけが quasicategory。coslice の弱可縮性を Kan 性込みの条件へ強めない。
使われ方：Kerodon Theorem 7.2.3.1(2)（Tag 02NY）、HTT Theorem 4.1.3.1、随伴と Kan 拡張の cofinality 判定。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：全ての coslice 引き戻しが弱可縮なら射は right cofinal。
方針：right fibration への因子分解の左因子の引き戻しで条件を移し、右因子の trivial Kan 性を得る。
規約：元の始域の quasicategory 性は不要。
使われ方：Quillen A の right 側の十分性。 -/
lemma isRightCofinal_of_weaklyContractible_coslices {A B : SSet.{u}} [Quasicategory B]
    (f : A ⟶ B)
    (hc : ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f := by
  obtain ⟨M, j, p, hm, hj, hp, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.exists_rightAnodyne_rightFibration_factorization f
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := hp
  have hM : ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b))) := by
    intro b
    let i : Over.mk f ⟶ Over.mk p := Over.homMk j he
    have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_overPullback_rightAnodyne
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)) i hj
    have hw := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne _ hi).isWeakHomotopyEquivalence
    exact hw.weaklyContractible_iff.mp (hc b)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightFibration_trivialKanFibration_of_weaklyContractible_coslices p hM
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne j hj).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration p)
  exact he ▸ h

/-- 概要：right cofinality は各 coslice 引き戻しの弱可縮性と同値。
方針：coslice 射影への引き戻しによる必要性と right fibration による十分性を合わせる。
規約：標的 B のみ quasicategory、始域 A は任意の単体集合。
使われ方：Kerodon Theorem 7.2.3.1(2)（Tag 02NY）、HTT Theorem 4.1.3.1 の right cofinal 版。 -/
@[kerodon 02NY]
lemma isRightCofinal_iff_weaklyContractible_coslices {A B : SSet.{u}} [Quasicategory B]
    (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f ↔ ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b))) :=
  ⟨fun hf b ↦ hf.coslice_isWeaklyContractible b, isRightCofinal_of_weaklyContractible_coslices f⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.1.3.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_weaklyContractible_coslices
