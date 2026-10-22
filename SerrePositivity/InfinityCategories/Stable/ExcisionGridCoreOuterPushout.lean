module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreDiagram

/-!
概要：元の入力が押し出しなら core 外側の同じ四角形も押し出しとなる。
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

lemma ExcisionSquareGrid.core_outer_pushout {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionSquareGrid R z) (hR : IsPushoutSquare R) :
    IsPushoutSquare (grid22Face (excisionGridCoreDiagram ≫ d.extension.core) 1 1) := by
  apply isPushoutSquare_grid22_outer
  · have h : grid22Face (excisionGridCoreDiagram ≫ d.extension.core) 2 2 = R := by
      change grid22Face excisionGridCoreDiagram 2 2 ≫ d.extension.core = R
      rw [excisionGridCoreDiagram_lowerLeft]
      simp only [Category.assoc, d.extension.seed_eq, d.square_eq, Iso.inv_hom_id_assoc]
    rwa [h]
  · change IsPushoutSquare (grid22Face excisionGridCoreDiagram 0 2 ≫ d.extension.core)
    rw [excisionGridCoreDiagram_lowerRight]
    exact d.extension.lower_right_pushout
  · change IsPushoutSquare (grid22Face excisionGridCoreDiagram 2 0 ≫ d.extension.core)
    rw [excisionGridCoreDiagram_upperLeft, Category.assoc]
    exact (isPushoutSquare_iff_transpose _).mp d.extension.upper_right_pushout
  · change IsPushoutSquare (grid22Face excisionGridCoreDiagram 0 0 ≫ d.extension.core)
    rw [excisionGridCoreDiagram_upperRight]
    exact d.extension.center_pushout

end SerrePositivity.InfinityCategories
