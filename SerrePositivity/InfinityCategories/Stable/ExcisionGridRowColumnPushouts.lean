module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridRowColumnFaces

/-!
概要：三面の貼り合わせから残る大きな二四角形の押し出し性を得る。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma ExcisionGridExtension.row_outer_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsPushoutSquare (strip3Square (excisionGridRowStrip ≫ d.full) 1 1) := by
  apply isPushoutSquare_strip3_outer
  · change IsPushoutSquare (strip3Square excisionGridRowStrip 3 2 ≫ d.full)
    rw [excisionGridRowStrip_first]
    simpa only [pastingSquare, Category.assoc, d.middle_eq, d.core_eq] using
      (isPushoutSquare_iff_transpose _).mp d.upper_right_pushout
  · change IsPushoutSquare (strip3Square excisionGridRowStrip 3 0 ≫ d.full)
    rw [excisionGridRowStrip_second]
    simpa only [pastingSquare, Category.assoc, d.middle_eq, d.core_eq] using d.center_pushout
  · change IsPushoutSquare (strip3Square excisionGridRowStrip 0 0 ≫ d.full)
    rw [excisionGridRowStrip_third]
    exact d.right_pushout

lemma ExcisionGridExtension.column_outer_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsPushoutSquare (strip3Square (excisionGridColumnStrip ≫ d.full) 1 1) := by
  apply isPushoutSquare_strip3_outer
  · change IsPushoutSquare (strip3Square excisionGridColumnStrip 3 2 ≫ d.full)
    rw [excisionGridColumnStrip_first]
    simpa only [pastingSquare, Category.assoc, d.middle_eq, d.core_eq] using
      (isPushoutSquare_iff_transpose _).mp d.lower_right_pushout
  · change IsPushoutSquare (strip3Square excisionGridColumnStrip 3 0 ≫ d.full)
    rw [excisionGridColumnStrip_second]
    simpa only [pastingSquare, Category.assoc, d.middle_eq, d.core_eq] using
      (isPushoutSquare_iff_transpose _).mp d.center_pushout
  · change IsPushoutSquare (strip3Square excisionGridColumnStrip 0 0 ≫ d.full)
    rw [excisionGridColumnStrip_third]
    exact d.left_pushout

end SerrePositivity.InfinityCategories
