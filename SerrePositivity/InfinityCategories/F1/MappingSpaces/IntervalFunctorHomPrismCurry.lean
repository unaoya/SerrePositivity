module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFunctorHomPrism
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismFamilyCurry

/-!
概要：両端の図式を固定した prism を、元の関手圏の区間 Hom の族へ戻す。
方針：同じ prism を curry し、両端条件を内部 Hom の端点条件に移す。
規約：二方向の往復は全パラメーターで厳密な等式。
使われ方：分類先の固定成分 fiber の三辺固定の表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 両端で元の二つの図式に定値な prism を、同じ関手圏の区間 Hom に戻す。 -/
def intervalFunctorHomPrismCurry {T B X : SSet.{u}} {F G : B ⟶ X}
    (H : ((Δ[1] : SSet.{u}) ⊗ B) ⊗ T ⟶ X)
    (h₀ : (prismEndpoint 0 B ▷ T) ≫ H = fst B T ≫ F)
    (h₁ : (prismEndpoint 1 B ▷ T) ≫ H = fst B T ≫ G) :
    T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G) :=
  intervalMappingCurryOfEndpoints (functorParameterizedCurry H)
    (by
      apply uncurry_injective
      change uncurry (simplexPrismVertex 1 0 T ≫ functorParameterizedCurry H) = _
      rw [← functorParameterizedPrism_vertex, functorParameterizedPrism_curry]
      change (prismEndpoint 0 B ▷ T) ≫ H = uncurry (SSet.const (functorVertex F))
      rw [h₀, uncurry_const_functorVertex])
    (by
      apply uncurry_injective
      change uncurry (simplexPrismVertex 1 1 T ≫ functorParameterizedCurry H) = _
      rw [← functorParameterizedPrism_vertex, functorParameterizedPrism_curry]
      change (prismEndpoint 1 B ▷ T) ≫ H = uncurry (SSet.const (functorVertex G))
      rw [h₁, uncurry_const_functorVertex])

/-- 同じ両端固定の prism を Hom に戻して評価すると、元の prism を厳密に回収する。 -/
lemma intervalFunctorHomPrism_curry {T B X : SSet.{u}} {F G : B ⟶ X}
    (H : ((Δ[1] : SSet.{u}) ⊗ B) ⊗ T ⟶ X)
    (h₀ : (prismEndpoint 0 B ▷ T) ≫ H = fst B T ≫ F)
    (h₁ : (prismEndpoint 1 B ▷ T) ≫ H = fst B T ≫ G) :
    intervalFunctorHomPrism (intervalFunctorHomPrismCurry H h₀ h₁) = H := by
  unfold intervalFunctorHomPrism intervalFunctorHomPrismCurry
  rw [intervalMappingUncurry_curryOfEndpoints, functorParameterizedPrism_curry]

/-- 元の区間 Hom の全パラメーターの族を展開して戻すと、元の族を厳密に回収する。 -/
lemma intervalFunctorHomPrismCurry_prism {T B X : SSet.{u}} {F G : B ⟶ X}
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) :
    intervalFunctorHomPrismCurry (intervalFunctorHomPrism f)
      (intervalFunctorHomPrism_zero f) (intervalFunctorHomPrism_one f) = f := by
  apply intervalFunctorHomPrism_injective F G
  exact intervalFunctorHomPrism_curry _ _ _

end SerrePositivity.InfinityCategories
