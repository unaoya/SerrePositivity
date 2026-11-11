module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：始対象を持つ通常の圏の図式上の slice の、始対象での値への制限。
方針：始対象の頂点包含の left anodyne 性と A2c による slice の制限の充填性を使う。
規約：文言と向きは実装前に Core/README.md に固定したもの。
使われ方：HTT §4.1.1 の必要な場合、Kerodon §7.2.2（Tag 02NQ） と Corollary 4.3.6.14。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section

universe v w

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：通常の圏上の図式の slice を指定対象での値上の slice へ制限する。
方針：その対象の nerve への頂点包含で図式を前合成する。
規約：対象の宇宙 v と射の宇宙 w は独立。nerve と slice は SSet.{max v w}。
使われ方：HTT §4.1.1、Kerodon §7.2.2（Tag 02NQ） の始対象による制限。 -/
def initialRestriction {I : Type v} [Category.{w} I] {X : SSet.{max v w}}
    (F : nerve I ⟶ X) (c : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)

/-- 概要：始対象を持つ圏上の図式の slice の始対象への制限は trivial Kan fibration。
方針：始対象の頂点包含が left anodyne であることと、slice の制限の一般補題を使う。
規約：対象の宇宙 v と射の宇宙 w は独立。F は SSet.{max v w} の任意の射。
使われ方：HTT §4.1.1 の必要な場合、Kerodon §7.2.2（Tag 02NQ）・Corollary 4.3.6.14（Tag 018L）。 -/
lemma initialCofinality {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (initialRestriction F c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne hc)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
