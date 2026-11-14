module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralHomHolimComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.RepresentableLimitEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictNativeCocones
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の小圏上の極限性と余極限性を反転豊穣 Hom の end で判定する。
方針：一般の end と切断の同値を native な切断判定へ渡し、余錐では反対の錐へ双対化する。
規約：反転係数の比較 q′ を用い、Hom の厳密極限性や添字の形状の仮定を付けない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の一般形状の判定。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：任意の strict な錐の native な極限性は全ての反転豊穣比較 q′ の同値性と同値。
方針：切断比較による判定から一般の end の後合成同値を消去する。
規約：元の非反転 q_x への移送を仮定せず、反転係数の実際の end を使う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の一般の極限判定。 -/
@[kerodon 03BB]
lemma strictCoherentCone_isLimit_iff_reflectedRepresentableComparison {F : I ⥤ C}
    (c : Cone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) ↔ ∀ x : C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison]
  exact forall_congr' fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.reflectedStrictConeSectionsComparison_homotopyEquivalence_iff
    c x (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_homotopyEquivalence F x)

/-- 概要：元の標準図式上の native な余錐の余極限性は反対の反転豊穣比較で判定できる。
方針：native な余錐の双対判定と反対圏の一般の極限判定を合成する。
規約：余錐は元の図式上の strictNativeCocone を使い、添字の形状を制限しない。
使われ方：HTT 4.2.4.1、余積・homotopy 余極限への共通の判定。 -/
lemma strictNativeCocone_isColimit_iff_reflectedRepresentableComparison {F : I ⥤ C}
    (c : Cocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c) ↔ ∀ x : Cᵒᵖ,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c.op x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_isColimit_iff]
  exact strictCoherentCone_isLimit_iff_reflectedRepresentableComparison c.op

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
