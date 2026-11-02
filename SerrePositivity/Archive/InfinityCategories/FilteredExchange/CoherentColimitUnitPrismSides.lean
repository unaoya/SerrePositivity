module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTrianglePrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismSideTriangleYoneda
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTriangles

/-!
概要：元の単位三角柱の全側面を、既存の同じ上下単位三角形へ厳密に同定する。
方針：元の辺正方形への制限と座標交換による二標準三角形の交換を使う。
規約：元の精密化用二単体を保持。使われ方：三比較の合成則と native 比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 任意の元の辺上の上側面は、既存の同じ下単位三角形に厳密に一致する。 -/
lemma coherentColimitUnitTrianglePrism_upper (j : Fin 3)
    {U V : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy U V) (hf : stdSimplex.δ j ≫ T.diagram = curry H.h) :
    homotopyEdgeTriangleUpper (coherentColimitUnitTrianglePrism B T)
      ((Δ[2] : SSet.{u + 1}).δ j (SSet.yonedaEquiv (𝟙 Δ[2]))) =
        SSet.yonedaEquiv (coherentColimitUnitLowerTriangle B H).diagram := by
  have he : (stdSimplex.δ j ▷ (Δ[1] : SSet.{u + 1})) ≫
      coherentColimitUnitTrianglePrism B T =
        (β_ Δ[1] Δ[1]).hom ≫ coherentColimitUnitSquare B H := by
    rw [coherentColimitUnitTrianglePrism, ← Category.assoc, ← comp_whiskerRight,
      hf, coherentColimitUnitFamily_edge]
  rw [← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id,
    homotopyEdgeTriangleUpper_yoneda, he, ← Category.assoc, squareTriangle_swap]
  rfl

/-- 任意の元の辺上の下側面は、既存の同じ上単位三角形に厳密に一致する。 -/
lemma coherentColimitUnitTrianglePrism_lower (j : Fin 3)
    {U V : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy U V) (hf : stdSimplex.δ j ≫ T.diagram = curry H.h) :
    homotopyEdgeTriangleLower (coherentColimitUnitTrianglePrism B T)
      ((Δ[2] : SSet.{u + 1}).δ j (SSet.yonedaEquiv (𝟙 Δ[2]))) =
        SSet.yonedaEquiv (coherentColimitUnitUpperTriangle B H).diagram := by
  have he : (stdSimplex.δ j ▷ (Δ[1] : SSet.{u + 1})) ≫
      coherentColimitUnitTrianglePrism B T =
        (β_ Δ[1] Δ[1]).hom ≫ coherentColimitUnitSquare B H := by
    rw [coherentColimitUnitTrianglePrism, ← Category.assoc, ← comp_whiskerRight,
      hf, coherentColimitUnitFamily_edge]
  rw [← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id,
    homotopyEdgeTriangleLower_yoneda, he, ← Category.assoc, squareTriangle_swap]
  rfl

end SerrePositivity.InfinityCategories.F2
