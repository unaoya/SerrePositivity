module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinCells
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.Transport.PrismLiftSpace
public import SerrePositivity.InfinityCategories.F1.Universe.Prism
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.Compact.CoconeFiberPrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.Compact.CoconeUniverseImage
public import SerrePositivity.InfinityCategories.HomotopyLimits.Compact.CoconeUniverseImagePrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.Compact.CoconeUniversePrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.Compact.CoconeUniverseVertex
public import SerrePositivity.InfinityCategories.HomotopyLimits.Compact.UniverseCoconeRepresentations
public import SerrePositivity.InfinityCategories.F1.Compact.YonedaEvaluationClassification
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftFibration

/-!
概要：元の余錐の fiber 写像と、宇宙変更後の同じ余錐の fiber 写像を全自然同型で比較。
方針：同じ底と同じ始点を持つ二つの実 prism を、相対延長の終点一意性で結ぶ。
規約：元の二つの指定写像を、その同じ全空間比較と同じ実頂点同値を介して比較。
使われ方：指定した空間の宇宙変更の小さい余極限保存。
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

/-- 元の同じ fiber 写像の宇宙変更と、元の余錐像の同じ fiber 写像との全自然比較。 -/
def coconeUniverseFiberIso (c : JoinCocone F) :
    FunctorIso (coconeUniverseSourceComparison c ≫ coconeFiberMap (coconeUniverseImage c))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (coconeFiberMap c) ≫
        coconeUniverseVertexMap c) := by
  let a := uliftSimplexPrism.{u + 1, u + 2} (coconeFiberBasePrism (F := F)) ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map c.val ≫ spaceUniverseDiagram.{u}
  let v := (spaceUniverseCoconeSourceRepresentation c).pointedMap
  have hv : v ≫ pointedSpaceProjection = prismEndpoint 0 _ ≫ a := by
    rw [show v = prismEndpoint 0 _ ≫ coconeUniversePrism c from
      (coconeUniversePrism_zero c).symm, Category.assoc, coconeUniversePrism_projection]
  have h₁ : prismEndpoint 1 _ ≫ a =
      SSet.const (spaceUniverseDiagram.app _ (ULift.up c.vertex)) := by
    rw [show a = coconeUniversePrism c ≫ pointedSpaceProjection from
      (coconeUniversePrism_projection c).symm, ← Category.assoc,
      coconeUniversePrism_one_fiber, Category.assoc, Category.assoc,
      vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  exact relativeExtensionFiberEndpoint_witnessIso pointedSpaceProjection a (prismEndpoint 0 _)
    (prismEndpoint_zero_leftAnodyne _) v hv (prismEndpoint 1 _)
    (spaceUniverseDiagram.app _ (ULift.up c.vertex)) h₁
    (coconeUniverseImagePrism c) (coconeUniversePrism c)
    (coconeUniverseImagePrism_projection c) (coconeUniversePrism_projection c)
    (coconeUniverseImagePrism_zero c) (coconeUniversePrism_zero c)
    _ _ (coconeUniverseImagePrism_one c) (coconeUniversePrism_one_fiber c)

end SerrePositivity.InfinityCategories.F2.Compact
