module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralConeComparisonReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralReflectedCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableFiberCriterion

/-!
概要：任意の小圏上の native な極限・余極限を元の非反転 q_x とその導来 fiber で判定する。
方針：edgewise 共通解像による反転の照合を一般の native な判定へ接続する。
規約：Hom の厳密極限性・遷移の fibration 性・q_x の fibration 性を要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、γ3b の一般形状の可縮性による検出。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：任意の小圏上の豊穣 Hom の元の比較と反転比較の同値性は一致する。
方針：実際の Hom の錐に edgewise 共通解像の一般の判定を適用する。
規約：局所 Kan 性以外の形状や充填性の条件は不要。
使われ方：HTT 4.2.4.1、元の非反転 q_x による一般の判定への橋渡し。 -/
lemma representableComparison_reflection_general_iff {F : I ⥤ C} (c : Cone F) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c x) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x).pt :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom x c.pt))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_reflection_general_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x)

/-- 概要：任意の strict な錐の native な極限性は全ての元の q_x の同値性と同値。
方針：一般の反転比較による極限判定の各項を元の比較へ戻す。
規約：Hom の厳密極限性や添字の形状を仮定しない両向きの判定。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB）、homotopy 極限と ∞ 極限の比較。 -/
lemma strictCoherentCone_isLimit_iff_general_representableComparison {F : I ⥤ C}
    (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ x : C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedRepresentableComparison]
  exact forall_congr' fun x ↦ (representableComparison_reflection_general_iff c x).symm

/-- 概要：元の標準図式上の余錐の native な余極限性は反対の元の q_x の同値性と同値。
方針：余錐の双対判定を反対圏の一般の極限判定へ接続する。
規約：反転した係数の end を結論には残さない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、一般の homotopy 余極限の判定。 -/
lemma strictNativeCocone_isColimit_iff_general_representableComparison {F : I ⥤ C}
    (c : Cocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c) ↔ ∀ x : Cᵒᵖ,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c.op x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_isColimit_iff]
  exact strictCoherentCone_isLimit_iff_general_representableComparison c.op

/-- 概要：一般の native な極限性は元の非反転 q_x の全導来 fiber の可縮性と同値。
方針：一般の比較の同値性の判定を Kan 複体間の射の全導来 fiber の判定で書き換える。
規約：可縮性は strict な Hom の極限でなく q_x の導来 fiber に要求する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB）、A3d に基づく γ3b の一般の検出。 -/
lemma strictCoherentCone_isLimit_iff_general_comparisonFiber {F : I ⥤ C} (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ (x : C)
      (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)) _⦋0⦌),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) b) := by
  rw [strictCoherentCone_isLimit_iff_general_representableComparison]
  exact forall_congr' fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableComparison_iff_comparisonFiber_isContractibleKan c x

/-- 概要：一般の native な余極限性は反対の元の q_x の全導来 fiber の可縮性と同値。
方針：元の標準余錐を双対の一般の極限の fiber 判定へ移す。
規約：元の係数図式の Hom の厳密極限性や fibration 条件は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、γ3 の余極限側の可縮性判定。 -/
lemma strictNativeCocone_isColimit_iff_general_comparisonFiber {F : I ⥤ C} (c : Cocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c) ↔ ∀ (x : Cᵒᵖ)
      (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op x)) _⦋0⦌),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c.op x) b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_isColimit_iff]
  exact strictCoherentCone_isLimit_iff_general_comparisonFiber c.op

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
