module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleFamilyEdgeMap
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeFunctorRestrictedEndpoint

/-!
概要：同じ全三角形の長辺・最後の辺の終点評価を、元の全終点評価へ厳密に繋ぐ。
方針：辺の終点包含の一致と相対制限の合成則で同じ全族の評価を比較する。
規約：全係数・全初期値を保持。使われ方：固定面と第零面の指定比較の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K Q : SSet.{u + 1}} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) (scaffoldFirstVertex 2) p)
  (q : Q ⟶ SpaceInfinity.{u}) (a : E ⊗ K ⟶ Q)
  (hEnd : (simplexPrismVertex 2 2 E ▷ K) ≫ ((Δ[2] ◁ p) ▷ K) ≫ D.diagram = a ≫ q)
  (i : Fin 3) (hi : i ≠ 2)
local notation "b₂" => ((Δ[2] ◁ p) ▷ K) ≫ PointedTransportPrismFamily.diagram D
local notation "r" => (stdSimplex.δ i ▷ E) ▷ K

include hEnd hi in
/-- 長辺・最後の辺の全終点は、元の三角形と同じ標的図式を被覆する。 -/
lemma pointedTriangleFamilyEdgeBase_endpoint :
    (prismEndpoint 1 E ▷ K) ≫ (r ≫ b₂) = a ≫ q := by
  rw [← Category.assoc, triangleFamilyEdge_terminal E K i hi]
  exact hEnd

/-- 元の同じ相対辺を、同じ全パラメータの標的の全空間へ評価する。 -/
def pointedTriangleFamilyEdgeEndpointMap :=
  relativeFunctorRestrictedEndpoint pointedSpaceProjection (r ≫ b₂)
    (prismEndpoint 1 E ▷ K) q a (pointedTriangleFamilyEdgeBase_endpoint D q a hEnd i hi)

/-- 同じ辺を経た全終点評価は、元の全三角形の指定終点評価そのもの。 -/
lemma pointedTriangleFamilyEdgeEndpoint_factor :
    pointedTriangleFamilyEdgeMap D i ≫ pointedTriangleFamilyEdgeEndpointMap D q a hEnd i hi =
    relativeFunctorExtensionEndpoint pointedSpaceProjection b₂
      ((scaffoldFirstVertex 2 ▷ E) ▷ K) D.boundary D.projection
      (simplexPrismVertex 2 2 E ▷ K) q a hEnd := by
  unfold pointedTriangleFamilyEdgeMap pointedTriangleFamilyEdgeEndpointMap
  rw [Category.assoc, relativeFunctorRestrictedEndpoint_pre,
    ← relativeFunctorExtensionEndpoint_factor]
  apply congrArg (fun z => relativeFunctorExtensionSpaceι pointedSpaceProjection b₂
    ((scaffoldFirstVertex 2 ▷ E) ▷ K) D.boundary D.projection ≫ z)
  exact relativeFunctorRestrictedEndpoint_congr pointedSpaceProjection b₂ q a
    (triangleFamilyEdge_terminal E K i hi)
    (by rw [Category.assoc]; exact pointedTriangleFamilyEdgeBase_endpoint D q a hEnd i hi) hEnd

end SerrePositivity.InfinityCategories.F2
