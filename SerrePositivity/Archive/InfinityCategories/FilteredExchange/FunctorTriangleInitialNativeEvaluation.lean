module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleInitialEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceComparison

/-!
概要：全初期値固定の辺の始点に元の native 作用を施した全族も、同じ頂点に定値となる。
方針：元の始点評価の定値性と相対後合成の厳密な頂点式を使う。
規約：元の選択済み作用を保持。使われ方：第一辺・長辺の native 比較の恒等性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J Q : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
  (H : SSet.Homotopy F Q) (i : Fin 3) (hFace : stdSimplex.δ i ≫ T.diagram = curry H.h)
local notation "P" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection Q)
  (Subtype.val (leftUnstraighteningMappingVertexMap F Q (coherentVertexOfHomotopy H)))
  (Subtype.property (leftUnstraighteningMappingVertexMap F Q (coherentVertexOfHomotopy H))) p
local notation "z" => functorHomotopySourceCanonicalWitness H p s hi

/-- 元の固定始点の辺の native 始点像は、同じ元の普遍証拠の実終点の頂点へ定値。 -/
lemma FunctorTrianglePointedWitness.edgeNative_constant
    (hStart : prismEndpoint 0 C ≫ (stdSimplex.δ i ▷ C) = simplexPrismVertex 2 0 C) :
    w.edgeMap H i hFace ≫ (functorHomotopyPrismSourceEvaluation H p ≫ P) =
      (SSet.const (relativeFunctorVertex (leftUnstraighteningProjection Q) p
        (z).endpoint (z).endpoint_over) : w.choice ⟶ _) := by
  rw [← Category.assoc, w.edgeSource_constant hi H i hFace hStart, SSet.const_comp]
  exact congrArg SSet.const (relativeFunctorPost_vertex _ _ _
    (leftUnstraighteningMappingVertexMap F Q (coherentVertexOfHomotopy H)).property p s hi)

end SerrePositivity.InfinityCategories.F2
