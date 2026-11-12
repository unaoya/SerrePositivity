module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport

/-!
概要：一つの極限錐の後合成の極限性から、同じ図式の全ての極限錐の保存を導く。
方針：図式上の二つの極限錐の同型を後合成の slice 写像で移し、終対象性を輸送する。
規約：任意の coherent な錐を扱い、strict な錐への選び直しを前提にしない。
使われ方：HTT 4.2.4.1・5.2.4.6、具体的な標準極限錐から全ての極限錐への保存の拡張。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：一つの極限錐を保存する関手は同じ図式の全ての極限錐を保存する。
方針：二つの極限錐の h(slice) での同型を後合成で写し、既知の像の極限性を移す。
規約：関手 f の同値性や全ての図式の極限保存は要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、strict な表示での検証を任意の coherent な極限錐へ拡張する。 -/
lemma isLimitCone_postcomp_of_one_limitCone {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : K ⟶ X} (f : X ⟶ Y)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (hfc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.postcomp f))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (d.postcomp f) := by
  exact hfc.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeIso c d hc hd) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p f))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
