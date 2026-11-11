module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleBaseFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawTransportPointPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ConstantDiagramTransportCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.F1DiagramsTrianglePrism

/-!
概要：元の全定値三角形上で、最初辺を固定し最後辺を元の raw 普遍輸送にする。
方針：同じ実中間頂点と全底の一致を示し、内ホーン prism を充填する。
規約：元の指定二単体と最初辺を保持。使われ方：長辺と最後辺の指定比較の同時照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
/-- 同じ raw 余錐頂点を持つ元の底上の定値図式。 -/
def coherentColimitRawConstantDiagram (B : SSet.{u})
    (F : Functor.obj SSet.uliftFunctor.{u + 1, u} B ⟶ SpaceInfinity.{u}) :
    Functor.obj SSet.uliftFunctor.{u + 1, u} B ⟶ SpaceInfinity.{u} :=
  SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F))

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

/-- 元の全三角形上に、元の最初辺と最後辺の同じ raw 普遍輸送を持つ全持ち上げがある。 -/
lemma exists_coherentColimitTriangleRawLastLift :
    ∃ W : (Δ[2] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u},
      (stdSimplex.δ (2 : Fin 3) ▷ E) ≫ W = H₀₁ ∧
      (stdSimplex.δ (0 : Fin 3) ▷ E) ≫ W = H₁₂ ∧ W ≫ pointedSpaceProjection = β := by
  have hw : prismEndpoint 1 E ≫ H₀₁ = prismEndpoint 0 E ≫ H₁₂ := by
    rw [functorHomotopyPointedPrism_target, coherentColimitRawTransportPointPrism_start]
    simp only [Category.id_comp, Category.assoc]
    exact (congrArg (fun q => ma ≫ q)
      (constantUnstraighteningFiberProjection_ι
        (Functor.obj SSet.uliftFunctor.{u + 1, u} B)
        (JoinCocone.vertex (coherentDiagramTotalCocone G)))).symm
  have hfirst : H₀₁ ≫ pointedSpaceProjection =
      (stdSimplex.δ (2 : Fin 3) ▷ E) ≫ β := by
    rw [functorHomotopyPointedPrism_projection, Category.id_comp]
    exact (coherentColimitConstantPrism_base B a _).trans
      (coherentColimitConstantTriangle_first_base B T _).symm
  have hlast : H₁₂ ≫ pointedSpaceProjection =
      (stdSimplex.δ (0 : Fin 3) ▷ E) ≫ β := by
    exact (coherentColimitRawTransportPointPrism_projection B b _).trans
      (coherentColimitConstantTriangle_last_base B T _).symm
  exact innerFibration_fillTrianglePrism pointedSpaceProjection H₀₁ H₁₂ β hw hfirst hlast

end SerrePositivity.InfinityCategories.F2
