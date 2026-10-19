module
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEquivalence

/-! # 通常の h と H⁰ の比較の実辺での公式

概要：通常の h の指定辺の類は、その閉射の H⁰ 類へ送られる。
方針：道の商から辺の類の商への比較を生成辺で評価する。
規約：端点も元の実頂点のまま。使われ方：H⁰ の等号から実合成二単体への帰還。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 通常の h の実辺の類の比較像は、同じ閉射の H⁰ 類。 -/
lemma dgStableHomotopyEquivalence_map_homMk {x y : (dgNerve A D) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A D)) x y) :
    (dgStableHomotopyEquivalence A D).functor.map
      (Truncated.HomotopyCategory.homMk e) = (toHomotopy A D).map (edgeClosed e) := by
  change (toH0 A D).map ((pathToEdgeHomotopyCategory _).map
    (Truncated.HomotopyCategory.homMk e)) = _
  simp only [pathToEdgeHomotopyCategory, Truncated.HomotopyCategory.lift_map_homMk]
  rfl

end SerrePositivity.InfinityCategories
