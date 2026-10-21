module

public import SerrePositivity.InfinityCategories.F2.InitialShapeConeCriterion

/-!
概要：一点と、始点への left anodyne 制限を持つ形状では任意の図式が極限を持つ。
方針：一点の恒等錐を元の形状へ自明 Kan 制限の切断で延長する。
規約：元の図式を厳密に固定。使われ方：有限形状の極限存在と交換の同時帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 一点上の任意の元の図式は恒等錐から極限を持つ。 -/
lemma hasLimit_point {X : SSet.{u}} [Quasicategory X] (p : (Δ[0] : SSet.{u}) ⟶ X) :
    HasLimit p := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  exact ⟨sliceIdentityCone x, F1B.kanSliceIdentityCone_isTerminalVertex x⟩

/-- 始点で極限を検出できる形状の任意の元の図式は極限を持つ。 -/
lemma hasLimit_of_initialShape {K X : SSet.{u}} [Quasicategory X]
    (a : (Δ[0] : SSet.{u}) ⟶ K) [Mono a] (ha : leftAnodyneExtensions a) (p : K ⟶ X) :
    HasLimit p := by
  have := sliceOverRestrict_trivialKanFibration p a ha
  obtain ⟨d, hd⟩ := hasLimit_point (a ≫ p)
  obtain ⟨c, hc, _, _⟩ := exists_limitCone_extension_of_trivialRestriction p a d hd
  exact ⟨c, hc⟩

end SerrePositivity.InfinityCategories.F2
