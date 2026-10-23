module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeUniversePrism
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeVertexFiberIso
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentationPointedFiber
public import SerrePositivity.InfinityCategories.F1.Universe.Fiber

/-!
概要：宇宙変更後の元の prism の終点を、同じ指定頂点の fiber の同値に分解する。
方針：元の頂点 fiber 同型・宇宙持ち上げ・同じ全余錐の表現の fiber 比較を合成。
規約：比較する射は元の指定頂点の包含と元の一つの pointed 写像の合成を厳密に回収。
使われ方：元の fiber 写像と、宇宙変更後の同じ余錐の fiber 写像の全自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} [Quasicategory B] {F : B ⟶ SpaceInfinity.{u}}

/-- 元の右包含上の値は、指定した元の頂点の同じ宇宙変更。 -/
lemma coconeUniverseVertex_value (c : JoinCocone F) :
    (spaceUniverseTransportRepresentation c.val).diagram.app _
      (ULift.up (SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u + 1})))) =
        spaceUniverseDiagram.app _ (ULift.up c.vertex) := by
  change spaceUniverseDiagram.app _ (ULift.up (c.val.app _ _)) = _
  rw [coconeFiberVertex_value]

/-- 指定頂点の元の fiber から、同じ元の頂点の宇宙変更後の fiber への実比較。 -/
def coconeUniverseVertexMap (c : JoinCocone F) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj
      (vertexFiber pointedSpaceProjection c.vertex) ⟶
        vertexFiber pointedSpaceProjection (spaceUniverseDiagram.app _ (ULift.up c.vertex)) :=
  ((SSet.uliftFunctor.{u + 2, u + 1}).mapIso (coconeVertexFiberIso c)).hom ≫
    (uliftVertexFiberIso.{u + 1, u + 2} (leftUnstraighteningProjection c.val) _).hom ≫
      representationPointedFiberMap (spaceUniverseTransportRepresentation c.val) _ ≫
        (vertexFiberPointIso pointedSpaceProjection (coconeUniverseVertex_value c)).hom

/-- 実際の頂点比較射は、元の指定包含を同じ一つの pointed 表現で送った射を回収する。 -/
lemma coconeUniverseVertexMap_ι (c : JoinCocone F) :
    coconeUniverseVertexMap c ≫ vertexFiberι pointedSpaceProjection
      (spaceUniverseDiagram.app _ (ULift.up c.vertex)) =
        (SSet.uliftFunctor.{u + 2, u + 1}).map (coconeFiberVertexInclusion c) ≫
          (spaceUniverseTransportRepresentation c.val).pointedMap := by
  simp only [coconeUniverseVertexMap, Category.assoc, vertexFiberPointIso_hom_ι,
    representationPointedFiberMap_ι]
  rw [← Category.assoc
    ((uliftVertexFiberIso.{u + 1, u + 2} (leftUnstraighteningProjection c.val) _).hom)
    (vertexFiberι _ _) _, uliftVertexFiberIso_hom_ι, ← Category.assoc,
    Functor.mapIso_hom, ← Functor.map_comp, coconeVertexFiberIso_hom_ι]

/-- 同じ実頂点比較射自身が同値であり、別の値の同値で代用しない。 -/
lemma coconeUniverseVertexMap_isQCatEquivalence (c : JoinCocone F) :
    IsQCatEquivalence (coconeUniverseVertexMap c) :=
  (qCatEquivalenceOfIso
    ((SSet.uliftFunctor.{u + 2, u + 1}).mapIso (coconeVertexFiberIso c))).isQCatEquivalence.comp
    ((qCatEquivalenceOfIso (uliftVertexFiberIso.{u + 1, u + 2}
      (leftUnstraighteningProjection c.val) _)).isQCatEquivalence.comp
      ((representationPointedFiberMap_isQCatEquivalence
        (spaceUniverseTransportRepresentation c.val) _).comp
          (qCatEquivalenceOfIso (vertexFiberPointIso pointedSpaceProjection
            (coconeUniverseVertex_value c))).isQCatEquivalence))

/-- 元の prism の同じ終点は、元の fiber 写像と同じ実頂点同値の合成。 -/
lemma coconeUniversePrism_one_fiber (c : JoinCocone F) :
    prismEndpoint 1 _ ≫ coconeUniversePrism c =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (coconeFiberMap c) ≫
        coconeUniverseVertexMap c ≫ vertexFiberι pointedSpaceProjection
          (spaceUniverseDiagram.app _ (ULift.up c.vertex)) := by
  rw [coconeUniverseVertexMap_ι, coconeUniversePrism_one]

end SerrePositivity.InfinityCategories.F2.Compact
