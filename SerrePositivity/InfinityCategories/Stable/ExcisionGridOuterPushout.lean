module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridOuterDiagram

/-!
概要：full 格子の四面から元の終点を始点とする外側の押し出し性を得る。
方針：実際の長方形の貼り合わせと同じ図式の評価を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma ExcisionGridExtension.final_outer_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsPushoutSquare (grid22Face (excisionGridOuterDiagram ≫ d.full) 1 1) := by
  apply isPushoutSquare_grid22_outer
  · change IsPushoutSquare (grid22Face excisionGridOuterDiagram 2 2 ≫ d.full)
    rw [excisionGridOuterDiagram_lowerLeft]
    simpa only [Category.assoc, d.middle_eq, d.core_eq] using d.center_pushout
  · change IsPushoutSquare (grid22Face excisionGridOuterDiagram 0 2 ≫ d.full)
    rw [excisionGridOuterDiagram_lowerRight]
    exact d.right_pushout
  · change IsPushoutSquare (grid22Face excisionGridOuterDiagram 2 0 ≫ d.full)
    rw [excisionGridOuterDiagram_upperLeft, Category.assoc]
    exact (isPushoutSquare_iff_transpose _).mp d.left_pushout
  · change IsPushoutSquare (grid22Face excisionGridOuterDiagram 0 0 ≫ d.full)
    rw [excisionGridOuterDiagram_upperRight]
    exact d.final_pushout

end SerrePositivity.InfinityCategories
