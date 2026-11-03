module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Joins.JoinQuasicategory
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplexPrismFirstVertex
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.Universe.Prism
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.Compact.CoconeFiberPrism
public import SerrePositivity.InfinityCategories.F1.Compact.CoconeTotalPrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.Compact.UniverseCoconeRepresentations
public import SerrePositivity.InfinityCategories.HomotopyLimits.Compact.UniverseRepresentation
public import SerrePositivity.InfinityCategories.F1.Compact.YonedaEvaluationClassification
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftFibration

/-!
概要：元の指定 fiber 写像の全空間 prism を、同じ余錐の一つの宇宙変更表現で送る。
方針：同じ実 prism を持ち上げ、その同じ全空間の pointed 写像へ後合成する。
規約：元の始点・元の fiber 写像による終点・元の join 円柱を同時に保持。
使われ方：同じ始点を持つ宇宙変更後の元の prism との終点の全自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} [Quasicategory B] {F : B ⟶ SpaceInfinity.{u}}

/-- 同じ元の全空間 prism を、元の余錐全体の一つの pointed 表現で送る。 -/
def coconeUniversePrism (c : JoinCocone F) :
    (Δ[1] : SSet.{u + 2}) ⊗ (SSet.uliftFunctor.{u + 2, u + 1}).obj (leftUnstraightening F) ⟶
      PointedSpaceInfinity.{u + 1} :=
  uliftSimplexPrism.{u + 1, u + 2} (coconeFiberTotalPrism c) ≫
    (spaceUniverseTransportRepresentation c.val).pointedMap

/-- 宇宙変更後の実 prism の始点は、同じ図式部分から制限した pointed 写像そのもの。 -/
lemma coconeUniversePrism_zero (c : JoinCocone F) :
    prismEndpoint 0 _ ≫ coconeUniversePrism c =
      (spaceUniverseCoconeSourceRepresentation c).pointedMap := by
  change simplexPrismVertex 1 0 _ ≫ _ = _
  rw [coconeUniversePrism, ← Category.assoc, uliftSimplexPrism_vertex]
  have h : simplexPrismVertex 1 0 _ ≫ coconeFiberTotalPrism c =
      leftUnstraighteningMap F c.val (joinInl B Δ[0]) c.property :=
    coconeFiberTotalPrism_zero c
  rw [h]
  exact (spaceUniverseCoconeSourceRepresentation_pointedMap c).symm

/-- 宇宙変更後の同じ終点は、元の指定 fiber 写像と元の指定頂点の包含の像を保持する。 -/
lemma coconeUniversePrism_one (c : JoinCocone F) :
    prismEndpoint 1 _ ≫ coconeUniversePrism c =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (coconeFiberMap c) ≫
        (SSet.uliftFunctor.{u + 2, u + 1}).map (coconeFiberVertexInclusion c) ≫
          (spaceUniverseTransportRepresentation c.val).pointedMap := by
  change simplexPrismVertex 1 1 _ ≫ _ = _
  rw [coconeUniversePrism, ← Category.assoc, uliftSimplexPrism_vertex]
  have h : simplexPrismVertex 1 1 _ ≫ coconeFiberTotalPrism c =
      coconeFiberMap c ≫ coconeFiberVertexInclusion c := coconeFiberTotalPrism_one c
  rw [h, Functor.map_comp, Category.assoc]

/-- 同じ宇宙変更後の prism は、元の join 円柱と元の全余錐像を厳密に被覆する。 -/
lemma coconeUniversePrism_projection (c : JoinCocone F) :
    coconeUniversePrism c ≫ pointedSpaceProjection =
      uliftSimplexPrism.{u + 1, u + 2} (coconeFiberBasePrism (F := F)) ≫
        (SSet.uliftFunctor.{u + 2, u + 1}).map c.val ≫ spaceUniverseDiagram.{u} := by
  rw [coconeUniversePrism, Category.assoc, LeftTransportRepresentation.pointedMap_projection]
  change uliftSimplexPrism.{u + 1, u + 2} (coconeFiberTotalPrism c) ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (leftUnstraighteningProjection c.val) ≫
      ((SSet.uliftFunctor.{u + 2, u + 1}).map c.val ≫ spaceUniverseDiagram.{u}) = _
  rw [← Category.assoc, uliftSimplexPrism_post, coconeFiberTotalPrism_projection]

end SerrePositivity.InfinityCategories.F2.Compact
