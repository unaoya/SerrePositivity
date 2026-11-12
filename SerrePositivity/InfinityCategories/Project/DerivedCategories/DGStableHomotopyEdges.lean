module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEquivalence

/-! # 通常の h と H⁰ の比較の実辺での公式

概要：通常の h の指定辺の類は、その閉射の H⁰ 類へ送られる。
方針：道の商から辺の類の商への比較を生成辺で評価する。
規約：端点も元の実頂点のまま。使われ方：H⁰ の等号から実合成二単体への帰還。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 通常の h の実辺の類の比較像は、同じ閉射の H⁰ 類。 -/
lemma dgStableHomotopyEquivalence_map_homMk {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A D).functor.map
      (Truncated.HomotopyCategory.homMk e) = (toHomotopy A D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 A D).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory _).map
    (Truncated.HomotopyCategory.homMk e)) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory, Truncated.HomotopyCategory.lift_map_homMk]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
