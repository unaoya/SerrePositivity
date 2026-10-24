module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowPrismAllBoundaryComparison
public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundaryUnder
public import SerrePositivity.InfinityCategories.F2.Ind.RightTensorCurrySource
/-!
概要：三境界固定の全円柱を、指定始点の全余錐の下で curry する。
方針：両側面固定の curry と始点評価の可換性を、同じ実 fiber へ持ち上げる。
規約：始点の全余錐・元の図式・元の終点図式を同時に保つ。
使われ方：Ind の補間比較を指定始点評価の下で反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {T X : SSet.{u}} (a : T ⊗ (Δ[1] : SSet.{u}) ⟶ X)
  (d : (Δ[1] : SSet.{u}) ⟶ X) (s : join T (Δ[0] : SSet.{u}) ⟶ X)
local notation "p" => SSet.yonedaEquiv.symm (functorVertex d)
local notation "b" => curry (CategoryTheory.Iso.hom (β_ (Δ[1]) T) ≫ a)
local notation "ev" => evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
/-- 概要：三固定条件を保った同じ円柱の全 curry。
方針：始点評価の実 fiber に持ち上げる。規約：指定全余錐を保持。使われ方：相対比較。 -/
def fixedArrowPrismAllBoundaryCurry : fixedArrowPrismAllBoundary a d s ⟶
    fixedCoconeBoundaryUnder p b ev s :=
  vertexFiberLift _ _
    (vertexFiberι (fixedArrowPrismSourceRestriction a d) (functorVertex s) ≫
      fixedArrowPrismBoundaryCurry a d) (by
        have hc : fixedArrowPrismBoundaryCurry a d ≫ fixedCoconeBoundaryInclusion p b =
            fixedArrowPrismBoundaryInclusion a d ≫
              rightTensorCurryMap (join T (Δ[0] : SSet.{u})) Δ[1] X :=
          vertexFiberLift_ι _ _ _ _
        rw [Category.assoc, ← Category.assoc (fixedArrowPrismBoundaryCurry a d),
          hc]
        simp only [Category.assoc]
        rw [rightTensorCurryMap_evaluate_zero]
        exact vertexFiberι_comp (fixedArrowPrismSourceRestriction a d) (functorVertex s))
end SerrePositivity.InfinityCategories.F2.Ind
