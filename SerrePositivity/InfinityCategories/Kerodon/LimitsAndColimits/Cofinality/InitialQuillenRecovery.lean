module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft

/-!
概要：left 側の Quillen A から単射による図式の slice 制限を判定し、A2h を回収する。
方針：弱可縮な slice 条件から left cofinality、単射の left anodyne 性、slice 制限へ進む。
規約：A2h の通常の圏の対象と射の宇宙は独立のまま保つ。
使われ方：B3 の cofinality 判定と既存の始対象による極限計算の接続。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：left cofinal な単射による図式の slice 制限は trivial Kan fibration。
方針：cofinal な単射の left anodyne 性と slice 制限の充填定理を使う。
規約：図式の値域 X だけが quasicategory。
使われ方：極限を計算する向きの cofinality と A2h の制限写像の橋。 -/
lemma sliceOverRestrict_trivialKanFibration_of_isLeftCofinal
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) [Mono i]
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal i) (F : B ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict F i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration F i hi.leftAnodyneExtensions

/-- 概要：弱可縮な slice 条件を満たす単射による図式の slice 制限は trivial Kan fibration。
方針：left 側の Quillen A の十分性を一般の制限定理に渡す。
規約：B と X は quasicategory、A は任意。
使われ方：Quillen A による極限図式の形状の比較と A2h の特殊化。 -/
lemma sliceOverRestrict_trivialKanFibration_of_weaklyContractible_slices
    {A B X : SSet.{u}} [Quasicategory B] [Quasicategory X] (i : A ⟶ B) [Mono i]
    (hi : ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))))
    (F : B ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict F i) :=
  sliceOverRestrict_trivialKanFibration_of_isLeftCofinal i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices i hi) F

/-- 概要：通常の圏の始対象の頂点包含は Quillen A の弱可縮な slice 条件を満たす。
方針：既存の始対象の包含の left cofinality に、Quillen A の必要性を適用する。
規約：対象の宇宙 v と射の宇宙 w は独立、nerve は max v w。
使われ方：A2h を一般の Quillen A の判定に特殊化する際の条件。 -/
lemma nervePoint_initial_quillen_slice_condition {I : Type v} [Category.{w} I] {c : I}
    (hc : IsInitial c) (b : (nerve I : SSet.{max v w}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.nervePoint_isLeftCofinal hc).slice_isWeaklyContractible b

/-- 概要：A2h の始対象への元の slice 制限の trivial Kan 性を Quillen A 経由で回収する。
方針：始対象の包含の弱可縮条件を left 側の判定に戻し、単射による制限定理を使う。
規約：initialCofinality の結論と同じ写像・同じ二宇宙の型。始対象の包含の証拠は既存の定理を使う。
使われ方：B3 の一般の cofinality の判定と A2h の実際の制限写像の接続。 -/
lemma initialCofinality_via_quillenA {I : Type v} [Category.{w} I] {c : I}
    (hc : IsInitial c) {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction F c) :=
  sliceOverRestrict_trivialKanFibration_of_weaklyContractible_slices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)
    (nervePoint_initial_quillen_slice_condition hc) F

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
