module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleComparisonValues

/-!
概要：元の全三角形の中間評価を、右辺の始点と第一辺の終点に厳密に揃える。
方針：元の同じ全延長族を中間頂点で評価し、二射影と辺制限の展開で比較する。
規約：全係数と実中間頂点を保持。使われ方：右辺の native 始点像の同定。
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

/-- 元の全延長の実中間頂点を、元の同じ中間図式の全空間へ評価する。 -/
def FunctorTrianglePointedWitness.middleMap :
    w.choice ⟶ relativeFunctorSpace (leftUnstraighteningProjection G) p :=
  relativeFunctorExtensionEndpoint pointedSpaceProjection base (scaffoldFirstVertex 2 ▷ C)
    (snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F) w.start_projection
    (simplexPrismVertex 2 1 C) G p (functorTrianglePrism_middle_base T p)

/-- 元の中間評価の各点は、元の同じ実中間頂点射そのもの。 -/
lemma FunctorTrianglePointedWitness.middleMap_vertex (w' : FunctorTrianglePointedWitness T p s) :
    w.middleMap.app _ (w.point w') = relativeFunctorVertex (leftUnstraighteningProjection G) p
      w'.middle w'.middle_projection :=
  relativeFunctorExtensionEndpoint_vertex pointedSpaceProjection base (scaffoldFirstVertex 2 ▷ C)
    (snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F) w.start_projection
    (simplexPrismVertex 2 1 C) G p (functorTrianglePrism_middle_base T p)
    w'.prism w'.projection w'.start w'.middle w'.middle_projection w'.middle_pointed

/-- 元の右辺の全始点評価は、元の同じ全三角形の中間評価そのもの。 -/
lemma FunctorTrianglePointedWitness.rightSource_factor :
    w.edgeMap b 0 T.face_zero ≫ functorHomotopyPrismSourceEvaluation b p = w.middleMap := by
  have hv : prismEndpoint 0 C ≫ (stdSimplex.δ (0 : Fin 3) ▷ C) =
      simplexPrismVertex 2 1 C := by
    apply SSet.hom_ext
    intro n
    rfl
  unfold FunctorTrianglePointedWitness.middleMap
  rw [← relativeFunctorExtensionEndpoint_factor]
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [functorHomotopyPrismSourceEvaluation, relativeFunctorRestrictedEndpoint_uncurry,
      relativeFunctorRestrictedEndpoint_uncurry, w.edgeMap_uncurry b 0 T.face_zero,
      ← Category.assoc, ← comp_whiskerRight, hv]
  · exact (relativeFunctorUncurry_projection _).trans (relativeFunctorUncurry_projection _).symm

/-- 元の第一辺の全終点評価も、元の同じ全三角形の中間評価そのもの。 -/
lemma FunctorTrianglePointedWitness.firstTarget_factor :
    w.edgeMap a 2 T.face_two ≫ functorHomotopyPrismTargetEvaluation a p = w.middleMap := by
  have hv : prismEndpoint 1 C ≫ (stdSimplex.δ (2 : Fin 3) ▷ C) =
      simplexPrismVertex 2 1 C := by
    apply SSet.hom_ext
    intro n
    rfl
  unfold FunctorTrianglePointedWitness.middleMap
  rw [← relativeFunctorExtensionEndpoint_factor]
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [functorHomotopyPrismTargetEvaluation, relativeFunctorRestrictedEndpoint_uncurry,
      relativeFunctorRestrictedEndpoint_uncurry, w.edgeMap_uncurry a 2 T.face_two,
      ← Category.assoc, ← comp_whiskerRight, hv]
  · exact (relativeFunctorUncurry_projection _).trans (relativeFunctorUncurry_projection _).symm

end SerrePositivity.InfinityCategories.F2
