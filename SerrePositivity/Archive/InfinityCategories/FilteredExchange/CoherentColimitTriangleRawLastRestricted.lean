module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitTriangleRawLastComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportPointPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFiberWitnessRestrictedPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportSource

/-!
概要：元の指定三角形と raw 普遍最終辺の持ち上げを、長辺と最後辺で同時に比較する。
方針：同じ最初辺を固定した全比較を二つの実辺へ制限する。
規約：元の二単体・全係数・実両端を保持。使われ方：長辺残余と一点輸送比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : Functor.obj SSet.uliftFunctor.{u + 1, u} B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "CF" => SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F))
local notation "CG" => SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone G))
local notation "E" => leftUnstraightening (coherentColimitRawConstantDiagram B F)
local notation "ma" => Subtype.val
  (leftUnstraighteningMappingVertexMap _ _ (coherentVertexOfHomotopy ca))
local notation "H₀₁" => functorHomotopyPointedPrism ca (𝟙 E)
local notation "H₁₂" => coherentColimitRawTransportPointPrism B b
  (ma ≫ coherentColimitRawConstantFiberProjection B G)
local notation "β" => (Δ[2] ◁ leftUnstraighteningProjection
  (coherentColimitRawConstantDiagram B F)) ≫
  functorSimplexDiagram (FunctorCompositionTriangle.diagram (coherentColimitConstantTriangle B T))

local notation "cb" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "mb" => Subtype.val
  (leftUnstraighteningMappingVertexMap _ _ (coherentVertexOfHomotopy cb))
local notation "W₀" => functorTrianglePointedLift (coherentColimitConstantTriangle B T)
local notation "j" => prismEndpoint 1 E ≫ (stdSimplex.δ (1 : Fin 3) ▷ E)
local notation "z" => JoinCocone.vertex (coherentDiagramTotalCocone J)

local notation "W₁" => coherentColimitTriangleRawLastPrism B T
local notation "g₀" => ma ≫ mb ≫ coherentColimitRawConstantFiberProjection B J
local notation "g₁" => (ma ≫ coherentColimitRawConstantFiberProjection B G) ≫
  coherentColimitRawFiberTransport B b

local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "w" => constantDiagramTransportWitness
  (constantDiagramMappingFamilyWitness (Functor.obj SSet.uliftFunctor B) A)
local notation "U" => pointedIntervalTransportSource P A
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift ma (SSet.const l)

/-- 元の最後辺の指定比較は、元の定値輸送と普遍輸送の同じ一点制限の指定比較。 -/
lemma coherentColimitTriangleRawLastLastComparison_heq_restricted :
    HEq (coherentColimitTriangleRawLastLastComparison B T)
      (fiberTransportRestrictedPrismComparison pointedSpaceProjection P
        (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U s) := by
  apply relativeFiberWitness_heq_restrictedPrism
  · rw [Category.assoc, functorTrianglePointedLift_projection]
  · rw [Category.assoc, coherentColimitTriangleRawLastPrism_projection]
  · rw [← Category.assoc, triangleFirstEdge_last_initial_square, Category.assoc,
      coherentColimitTriangleRawLast_original_first]
  · rw [← Category.assoc, triangleFirstEdge_last_initial_square, Category.assoc,
      coherentColimitTriangleRawLastPrism_first]
  · rw [← Category.assoc, triangleFirstEdge_last_final_square]
    exact coherentColimitTriangleRawLast_original_terminal B T
  · rw [← Category.assoc, triangleFirstEdge_last_final_square]
    exact coherentColimitTriangleRawLastPrism_terminal B T
  · calc
      _ = functorHomotopyPointedPrism cb ma := by
        simpa only [coherentColimitRawConstantDiagram,
          MonoidalCategory.whiskerLeft_id, Category.id_comp] using
          functorTrianglePointedLift_second (coherentColimitConstantTriangle B T) (𝟙 E)
      _ = _ := (coherentColimitConstantTransport_point_prism B b ma).symm
  · calc
      _ = coherentColimitRawTransportPointPrism B b (ma ≫ P) :=
        coherentColimitTriangleRawLastPrism_last B T
      _ = _ := (pointedIntervalTransportSource_point_prism P A ma l).symm

/-- 元の長辺の指定比較も、同じ元の二輸送の指定一点比較と値まで一致する。 -/
lemma coherentColimitTriangleRawLastLongComparison_heq_restricted :
    HEq (coherentColimitTriangleRawLastLongComparison B T)
      (fiberTransportRestrictedPrismComparison pointedSpaceProjection P
        (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U s) :=
  (heq_of_eq (coherentColimitTriangleRawLastLongComparison_eq_last B T)).trans
    (coherentColimitTriangleRawLastLastComparison_heq_restricted B T)

end SerrePositivity.InfinityCategories.F2
