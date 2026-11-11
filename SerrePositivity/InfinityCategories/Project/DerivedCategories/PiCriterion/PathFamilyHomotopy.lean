module

public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism

/-!
概要：指数 path の族を、同じ両端を持つ実際の円柱ホモトピーへ戻す。
方針：uncurry とテンソルの交換を使い、端点評価の計算式を適用する。
規約：族を選び直さず、源への制限と可換な円柱を返す。
使われ方：D の指定辺に沿う球面円柱の実現。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

/-- 指定 path の族をそのまま円柱に戻す。 -/
def pathFamilyHomotopy {K X : SSet.{u}} (r : K ⟶ KanPath.object X) :
    SSet.Homotopy (r ≫ KanPath.evaluation X 0) (r ≫ KanPath.evaluation X 1) where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry r
  h₀ := by
    change SSet.ι₀ ≫ ((β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry r) =
      r ≫ KanPath.evaluation X 0
    have hc := KanPath.curry_evaluation (uncurry r) (0 : Fin 2)
    rw [curry_uncurry] at hc
    have hi : SSet.ι₀ ≫ (β_ K (Δ[1] : SSet.{u})).hom =
        (λ_ K).inv ≫ KanPath.endpoint 0 ▷ K := rfl
    rw [← Category.assoc, hi]
    simpa only [Category.assoc] using hc.symm
  h₁ := by
    change SSet.ι₁ ≫ ((β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry r) =
      r ≫ KanPath.evaluation X 1
    have hc := KanPath.curry_evaluation (uncurry r) (1 : Fin 2)
    rw [curry_uncurry] at hc
    have hi : SSet.ι₁ ≫ (β_ K (Δ[1] : SSet.{u})).hom =
        (λ_ K).inv ≫ KanPath.endpoint 1 ▷ K := rfl
    rw [← Category.assoc, hi]
    simpa only [Category.assoc] using hc.symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- path の族の円柱実現は、元の源の射による制限と厳密に可換。 -/
lemma pathFamilyHomotopy_precomp {A K X : SSet.{u}} (i : A ⟶ K)
    (r : K ⟶ KanPath.object X) :
    i ▷ (Δ[1] : SSet.{u}) ≫ (pathFamilyHomotopy r).h =
      (pathFamilyHomotopy (i ≫ r)).h := by
  change i ▷ (Δ[1] : SSet.{u}) ≫ ((β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry r) = _
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
    ← uncurry_natural_left]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
