module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrecompositionOverColimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinLeftColimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverMono

/-!
概要：固定した終域上の写像円柱比較の連結な余極限への拡張。
方針：両関手の単射と余極限の保存を、Over 圏上の自然な比較の貼り合わせに適用する。
規約：自然数の列と小さいセルの族の wide pushout を扱う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、始域の全ての骨格とセルの族への帰納。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：骨格列の各項で円柱比較が同値条件を満たせば余極限でも満たす。
方針：二つの関手の単射と可算余極限の保存を自然な比較の貼り合わせに使う。
規約：遷移射は Over S の単射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、全ての有限骨格から全体への拡張。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_sequential_colimit
    {S : SSet.{u}} (D : ℕ ⥤ Over S)
    [∀ n, Mono (D.map (homOfLE (Nat.le_succ n)))]
    (c : Cocone D) (hc : IsColimit c)
    (h : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (D.obj n).hom)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison c.pt.hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_of_sequential_colimit
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparisonNat S) D c hc h

/-- 概要：セルの族を表す wide pushout の各項の円柱比較から余極限の比較が従う。
方針：二つの関手の単射と連結な余極限の保存を自然な比較の貼り合わせに使う。
規約：各枝の射は Over S の単射、族の添字は宇宙 u。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、同じ次元のセルの族の貼り合わせ。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_widePushout_colimit
    (J : Type u) {S : SSet.{u}} (D : WidePushoutShape J ⥤ Over S)
    [∀ j, Mono (D.map (.init j))] (c : Cocone D) (hc : IsColimit c)
    (h : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (D.obj j).hom)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison c.pt.hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_of_widePushout_colimit J
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparisonNat S) D c hc h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
