module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawVertices
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedCoherentFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback

/-!
概要：元の余極限三角形の初点 fiber に、元の全反転 Hom 係数を同値に写す。
方針：同じ初点の頂点等式で標準 coherent fiber 比較を厳密に移送する。
規約：元の全係数・実 fiber・包含を保持。使われ方：元の普遍三角形の全族の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "K₀" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))

/-- 元の実余錐頂点と同じ三角形の初点の coherent 表示の厳密な等式。 -/
lemma coherentColimitApexCoefficient_vertex :
    (coherentDiagramTotalCocone F).vertex = coherentNerveVertex K₀ :=
  (coherentColimitApex_raw_zero_vertex B T).trans (spaceInfinityVertex_eq_coherent K₀)

/-- 同じ全反転 Hom の係数から、元の実初点 fiber への指定比較。 -/
def coherentColimitApexCoefficientMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K₀).op ⟶
      vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex :=
  pointedCoherentFiberComparison K₀ ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (coherentColimitApexCoefficient_vertex B T).symm)

/-- 表示変更した全係数の比較も、元の全空間への包含を厳密に保つ。 -/
lemma coherentColimitApexCoefficientMap_ι :
    coherentColimitApexCoefficientMap B T ≫
      vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone F).vertex =
    pointedCoherentFiberComparison K₀ ≫
      vertexFiberι pointedSpaceProjection (coherentNerveVertex K₀) := by
  rw [coherentColimitApexCoefficientMap, Category.assoc]
  exact congrArg (fun m => pointedCoherentFiberComparison K₀ ≫ m)
    (vertexFiberTransport_ι pointedSpaceProjection
      (coherentColimitApexCoefficient_vertex B T).symm)

/-- 元の全係数の比較は同値であり、この前合成で指定比較の等式を反映できる。 -/
lemma coherentColimitApexCoefficientMap_isQCatEquivalence :
    IsQCatEquivalence (coherentColimitApexCoefficientMap B T) :=
  (pointedCoherentFiberComparison_isQCatEquivalence K₀).comp
    (qCatEquivalenceOfIso (eqToIso (congrArg (vertexFiber pointedSpaceProjection)
      (coherentColimitApexCoefficient_vertex B T).symm))).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2
