module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismOld

/-!
概要：元の図式側と余錐頂点上の全区間を共に固定する、全円柱の関手空間の実 fiber。
方針：二つの円柱制限を内部 Hom の積へ束ね、同じ指定頂点上の fiber を取る。
規約：途中で固定条件を忘れない。使われ方：元の q の全変換の指定境界比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の全円柱の二つの全区間側面への制限の対。 -/
def arrowPrismBoundaryRestriction (T X : SSet.{u}) :
    (ihom (join T (Δ[0] : SSet.{u}) ⊗ Δ[1])).obj X ⟶
      (ihom (T ⊗ Δ[1])).obj X ⊗ (ihom ((Δ[0] : SSet.{u}) ⊗ Δ[1])).obj X :=
  lift ((pre (joinInl T (Δ[0] : SSet.{u}) ▷ Δ[1])).app X)
    ((pre (joinInr T (Δ[0] : SSet.{u}) ▷ Δ[1])).app X)

/-- 元の図式側と同じ指定全区間を同時に固定した、元の全円柱の実 fiber。 -/
def fixedArrowPrismBoundary {T X : SSet.{u}} (a : T ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (d : (Δ[1] : SSet.{u}) ⟶ X) : SSet.{u} :=
  vertexFiber (arrowPrismBoundaryRestriction T X)
    (functorVertex a, functorVertex (snd (Δ[0] : SSet.{u}) Δ[1] ≫ d))

end SerrePositivity.InfinityCategories.F2.Ind
