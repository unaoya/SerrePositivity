module

public import SerrePositivity.InfinityCategories.F1.PrecompositionOverColimits
public import SerrePositivity.InfinityCategories.F1.RelativeJoinLeftColimits
public import SerrePositivity.InfinityCategories.F1.RelativeJoinCylinderNaturality
public import SerrePositivity.InfinityCategories.F1.MappingCylinderOverMono

/-!
概要：固定した終域上の写像円柱比較の連結な余極限への拡張。
方針：両関手の単射と余極限の保存を、Over 圏上の自然な比較の貼り合わせに適用する。
規約：自然数の列と小さいセルの族の wide pushout を扱う。
使われ方：Kerodon Proposition 5.2.4.5、始域の全ての骨格とセルの族への帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：骨格列の各項で円柱比較が同値条件を満たせば余極限でも満たす。
方針：二つの関手の単射と可算余極限の保存を自然な比較の貼り合わせに使う。
規約：遷移射は Over S の単射。
使われ方：Kerodon Proposition 5.2.4.5、全ての有限骨格から全体への拡張。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_sequential_colimit
    {S : SSet.{u}} (D : ℕ ⥤ Over S)
    [∀ n, Mono (D.map (homOfLE (Nat.le_succ n)))]
    (c : Cocone D) (hc : IsColimit c)
    (h : ∀ n, IsPrecompositionEquivalence (relativeJoinCylinderComparison (D.obj n).hom)) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison c.pt.hom) :=
  isPrecompositionEquivalence_over_of_sequential_colimit
    (relativeJoinCylinderComparisonNat S) D c hc h

/-- 概要：セルの族を表す wide pushout の各項の円柱比較から余極限の比較が従う。
方針：二つの関手の単射と連結な余極限の保存を自然な比較の貼り合わせに使う。
規約：各枝の射は Over S の単射、族の添字は宇宙 u。
使われ方：Kerodon Proposition 5.2.4.5、同じ次元のセルの族の貼り合わせ。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_widePushout_colimit
    (J : Type u) {S : SSet.{u}} (D : WidePushoutShape J ⥤ Over S)
    [∀ j, Mono (D.map (.init j))] (c : Cocone D) (hc : IsColimit c)
    (h : ∀ j, IsPrecompositionEquivalence (relativeJoinCylinderComparison (D.obj j).hom)) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison c.pt.hom) :=
  isPrecompositionEquivalence_over_of_widePushout_colimit J
    (relativeJoinCylinderComparisonNat S) D c hc h

end SerrePositivity.InfinityCategories
