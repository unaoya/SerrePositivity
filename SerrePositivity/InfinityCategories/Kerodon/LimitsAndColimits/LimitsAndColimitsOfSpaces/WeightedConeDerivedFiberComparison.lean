module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeRestriction

/-!
概要：反転した weighted な strict 錐と native な切断の制限の導来 fiber の実際の比較。
方針：全パラメータで可換な weighted 比較が導来 fiber に誘導する射を使う。
規約：反転係数と ULift 後の比較を使い、元の非反転 q_x との直接比較とは区別する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、錐の pinched Hom への直接比較。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：反転した切断比較の導来 fiber から native な切断の制限の導来 fiber への実際の射。
方針：weighted な錐全体の比較と制限の主可換式を導来 fiber の構成へ渡す。
規約：同じ coherent な切断の頂点 b を厳密に固定する。
使われ方：元の strict な錐の比較と native な錐の写像空間の直接の接続。 -/
noncomputable def weightedStrictConeFamilyFiberComparison {F : I ⥤ C}
    (c : Cone F) (x : C)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x) b ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedStrictConeFamilyComparison c x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedStrictConeFamilyComparison_restriction c x) b

/-- 概要：導来 fiber の比較は weighted な錐全体の比較と源射影上で可換。
方針：一般の導来 fiber の射の源成分の式を適用する。
規約：Kan 性や極限性は要求しない。
使われ方：切断の全パラメータの比較を導来 fiber の座標へ追跡する。 -/
lemma weightedStrictConeFamilyFiberComparison_source {F : I ⥤ C}
    (c : Cone F) (x : C)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) _⦋0⦌) :
    weightedStrictConeFamilyFiberComparison c x b ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedStrictConeSectionsComparison c x) b ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedStrictConeFamilyComparison c x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_source _ _ _ _ _

/-- 概要：局所 Kan な単体的圏では weighted な錐の実際の導来 fiber の比較射は同値。
方針：錐全体の weighted 比較の同値性を源の同値による導来 fiber の比較へ適用する。
規約：添字圏と錐は任意であり、Hom の fibration 性や厳密極限性は要求しない。
使われ方：錐の pinched Hom と表現可能な比較の導来 fiber の間の直接の比較 span。 -/
lemma weightedStrictConeFamilyFiberComparison_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (x : C)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (weightedStrictConeFamilyFiberComparison c x b) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_homotopyEquivalence _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedStrictConeFamilyComparison_homotopyEquivalence c x) b

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
