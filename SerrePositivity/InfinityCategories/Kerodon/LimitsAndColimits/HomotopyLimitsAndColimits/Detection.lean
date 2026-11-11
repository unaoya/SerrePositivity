module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal

/-!
概要：極限錐を、錐の圏の右 pinched 写像空間の可縮性で検出する。
方針：slice の終対象性に A3d を適用し、同型またはホモトピー同値で模型を移す。
規約：量化するのは全ての coherent な錐であり、strict な錐だけには制限しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の写像空間への帰着。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：極限錐へ向かう錐の右 pinched 写像空間は可縮。
方針：極限錐の定義を slice の終対象性として読む。
規約：この方向には標的の quasicategory 性は不要。
使われ方：HTT 4.2.4.1 の双対の必要条件。 -/
lemma isContractibleKan_conePinchedHom_of_isLimitCone {K X : SSet.{u}}
    {p : K ⟶ X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d c) :=
  hc.pinchedHom_isContractibleKan d

/-- 概要：極限性は全ての錐からの右 pinched 写像空間の可縮性と同値。
方針：slice の quasicategory 性の下で A3d の終対象判定を適用する。
規約：零次元も含む境界の充填を使い、写像空間の非空性も要求する。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、γ3b の検出部分。 -/
lemma isLimitCone_iff_conePinchedHom_isContractibleKan {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ ∀ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_pinchedHom_isContractibleKan (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c

/-- 概要：錐の写像空間の厳密な模型が全て可縮なら極限錐。
方針：同型で可縮性を戻して錐の写像空間の判定に渡す。
規約：模型との同型は全ての coherent な錐について必要。
使われ方：Kerodon 7.5.4.6（Tag 03BB） のファイバー模型との厳密な比較。 -/
lemma isLimitCone_of_conePinchedHom_iso {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (M : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p → SSet.{u})
    (e : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d c ≅ M d)
    (h : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (M d)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  apply (isLimitCone_iff_conePinchedHom_isContractibleKan c).2
  intro d
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (e d).symm (h d)

/-- 概要：錐の写像空間から可縮な Kan 模型へのホモトピー同値で極限性を検出する。
方針：Kan 複体間のホモトピー同値による可縮性の不変性を使う。
規約：模型の Kan 性と比較射の実際のホモトピー逆を明示する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の導来ファイバーとの比較を接続する界面。 -/
lemma isLimitCone_of_conePinchedHom_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (M : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p → SSet.{u})
    [∀ d, KanComplex (M d)] (f : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) d c ⟶ M d)
    (hf : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f d))
    (h : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (M d)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  apply (isLimitCone_iff_conePinchedHom_isContractibleKan c).2
  intro d
  exact (hf d).isContractibleKan_iff.mpr (h d)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
