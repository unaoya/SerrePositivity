module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanComparisonFibers
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.RepresentableLimitEquivalence

/-!
概要：指定三形状の native な ∞ 極限性を元の q_x の全導来 fiber の可縮性で検出する。
方針：元の比較射の同値性による両向きの判定と Kan 複体の導来 fiber の判定を接続する。
規約：元の q_x の fibration 性や Hom 錐の厳密極限性は要求しない。
使われ方：HTT 4.2.4.1 の限定形、Kerodon 7.5.4.6（Tag 03BB）、γ3b の可縮性への帰着。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：元の表現可能な比較 q_x の同値性は全導来 fiber の可縮性と同値。
方針：局所 Kan 性と Bousfield–Kan end の Kan 性を一般の fiber 判定へ渡す。
規約：ここでは添字圏や錐の形状を制限せず、極限性そのものはまだ主張しない。
使われ方：三形状の極限判定に元の q_x の導来 fiber を使う。 -/
lemma representableComparison_iff_comparisonFiber_isContractibleKan {F : I ⥤ C}
    (c : Cone F) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) ↔
      ∀ b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) b) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyEquivalence_iff_comparisonFiber_isContractibleKan _

/-- 概要：離散図式の実際の錐の ∞ 極限性は全ての元の q_x の導来 fiber の可縮性と同値。
方針：元の比較射の同値性による極限判定を各 x で fiber 判定へ移す。
規約：添字の有限性・非空性、Hom 錐の厳密極限性、q_x の fibration 性は不要。
使われ方：γ3b の積の可縮性による判定。 -/
lemma strictCoherentCone_isLimit_iff_discrete_comparisonFiber {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ (x : C)
      (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)) _⦋0⦌),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_discrete_representableComparison c]
  exact forall_congr' (fun x ↦ representableComparison_iff_comparisonFiber_isContractibleKan c x)

/-- 概要：Hom の一脚が fibration の cospan の ∞ 極限性は元の q_x の全導来 fiber の可縮性と同値。
方針：元の比較射による両向きの判定と全導来 fiber の判定を各 x で接続する。
規約：右脚の fibration 性、Hom 錐の厳密極限性、q_x の fibration 性は不要。
使われ方：γ3b の引き戻しの可縮性による判定。 -/
lemma strictCoherentCone_isLimit_iff_cospan_comparisonFiber
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F)
    [∀ x : C, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ (x : C)
      (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)) _⦋0⦌),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_cospan_representableComparison c]
  exact forall_congr' (fun x ↦ representableComparison_iff_comparisonFiber_isContractibleKan c x)

/-- 概要：Hom が fibration の塔をなす図式の ∞ 極限性は元の q_x の全導来 fiber の可縮性と同値。
方針：元の比較射の同値性を各底頂点の fiber の可縮性に読み替える。
規約：全隣接遷移の Hom の fibration 性だけを要求し、q_x 自身には要求しない。
使われ方：γ3b の塔の可縮性による判定。 -/
lemma strictCoherentCone_isLimit_iff_tower_comparisonFiber
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F)
    [∀ (x : C) (n : ℕ), Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ (x : C)
      (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)) _⦋0⦌),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_tower_representableComparison c]
  exact forall_congr' (fun x ↦ representableComparison_iff_comparisonFiber_isContractibleKan c x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
