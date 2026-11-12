module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.DiscreteComparison

/-!
概要：豊穣積の Hom 図式について、実際の標準比較射 q_x の同型性を示す。
方針：θ_x による分解と離散図式の κ_x の同型性を使う。
規約：coherent な錐の写像空間との比較はこの補題の結論に含めない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の有限積と空積。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Limits SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {J : Type u} {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：豊穣積の Hom の極限性から、標準比較射 q_x が厳密な同型になる。
方針：θ_x と離散図式の κ_x への分解に、同型の合成の性質を適用する。
規約：台の通常の積の普遍性だけではなく Hom 図式の極限性を要求する。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、γ3c の積での比較射の同値性。 -/
lemma representableHomotopyLimitComparison_discrete_isIso {F : Discrete J ⥤ C}
    (c : Cone F) (x : C) (h : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison_factorization c x h]
  infer_instance

/-- 概要：豊穣積の実際の表現可能な比較射はホモトピー同値。
方針：標準比較の厳密な同型性から逆射と定値ホモトピーを得る。
規約：積の添字の有限性や局所 Kan 性はこの計算には不要。
使われ方：HTT 4.2.4.1 の双対の積の場合の表現可能な判定の入力。 -/
lemma representableHomotopyLimitComparison_discrete_homotopyEquivalence
    {F : Discrete J ⥤ C} (c : Cone F) (x : C) (h : IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c x) := by
  have := representableHomotopyLimitComparison_discrete_isIso c x h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
