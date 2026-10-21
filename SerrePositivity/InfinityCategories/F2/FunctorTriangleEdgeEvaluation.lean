module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleEdgeComparison
public import SerrePositivity.InfinityCategories.F2.RelativeRestrictedEndpointUncurry
public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyPrismEvaluation

/-!
概要：元の全三角形の辺制限と終点評価を、元の同じ全終点評価へ厳密に因子分解する。
方針：全族の uncurry と二射影で元の同じ最終頂点への制限を比較する。
規約：全係数と指定比較の値を保持。使われ方：右辺の自然性を全終点比較へ繋ぐ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s)
local notation "base" => (Δ[2] ◁ p) ≫ functorSimplexDiagram T.diagram
local notation "I" => relativeFunctorExtensionSpaceι pointedSpaceProjection base
  (scaffoldFirstVertex 2 ▷ C) (snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F)
  (FunctorTrianglePointedWitness.start_projection w)

/-- 元の全辺制限の展開は、元の同じ全延長族の実辺制限そのもの。 -/
lemma FunctorTrianglePointedWitness.edgeMap_uncurry {Q R : B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy Q R) (i : Fin 3) (hFace : stdSimplex.δ i ≫ T.diagram = curry H.h) :
    relativeFunctorUncurry (w.edgeMap H i hFace) =
      ((stdSimplex.δ i ▷ C) ▷ w.choice) ≫ relativeFunctorUncurry I := by
  unfold FunctorTrianglePointedWitness.edgeMap
  rw [← Category.assoc]
  change relativeFunctorUncurry ((I ≫ relativeFunctorPre pointedSpaceProjection base
    (stdSimplex.δ i ▷ C)) ≫ (eqToIso (congrArg (relativeFunctorSpace pointedSpaceProjection)
      (functorTrianglePrism_edge_base T.diagram p i H hFace))).hom) = _
  rw [relativeFunctorUncurry_transport pointedSpaceProjection
    (functorTrianglePrism_edge_base T.diagram p i H hFace), relativeFunctorUncurry_pre]
  rfl

/-- 元の全延長の実終点を、元の同じ標的図式の全空間へ評価する。 -/
def FunctorTrianglePointedWitness.endpointMap :
    w.choice ⟶ relativeFunctorSpace (leftUnstraighteningProjection J) p :=
  relativeFunctorExtensionEndpoint pointedSpaceProjection base (scaffoldFirstVertex 2 ▷ C)
    (snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F) w.start_projection
    (simplexPrismVertex 2 2 C) J p (functorTrianglePrism_terminal_base T p)

/-- 終点を含む同じ辺を経る評価は、元の全三角形の同じ終点評価そのもの。 -/
lemma FunctorTrianglePointedWitness.edgeEndpoint_factor {Q : B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy Q J) (i : Fin 3) (hFace : stdSimplex.δ i ≫ T.diagram = curry H.h)
    (hEnd : prismEndpoint 1 C ≫ (stdSimplex.δ i ▷ C) = simplexPrismVertex 2 2 C) :
    w.edgeMap H i hFace ≫ functorHomotopyPrismTargetEvaluation H p = w.endpointMap := by
  unfold FunctorTrianglePointedWitness.endpointMap
  rw [← relativeFunctorExtensionEndpoint_factor]
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [functorHomotopyPrismTargetEvaluation, relativeFunctorRestrictedEndpoint_uncurry,
      relativeFunctorRestrictedEndpoint_uncurry, w.edgeMap_uncurry H i hFace,
      ← Category.assoc, ← comp_whiskerRight, hEnd]
  · exact (relativeFunctorUncurry_projection _).trans (relativeFunctorUncurry_projection _).symm

end SerrePositivity.InfinityCategories.F2
