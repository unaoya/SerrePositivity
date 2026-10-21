module

public import SerrePositivity.InfinityCategories.F2.CoherentTransformationTriangleRelative
public import SerrePositivity.InfinityCategories.F2.CoherentTotalObject

/-!
概要：元の恒等変換と合成三角形の小さい全空間作用を、指定単位の後で比較する。
方針：底上の相対同型から Kan 値への後合成へ直接移す。
規約：底の quasicategory 性は不要。指定変換・三角形・単位を保持する。
使われ方：有限 coherent 積の反復射影と元の単位の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の恒等辺を元の coherent 変換空間の頂点として表示する。 -/
def coherentIdentityTransformationVertex {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) : (leftUnstraighteningTransformationSpace F F) _⦋0⦌ :=
  intervalMappingVertexOfEdge (SSet.Edge.id (functorVertex F))

/-- 元の恒等変換の小さい作用は、元の単位の後で元の単位そのものと同型。 -/
def coherentIdentityTransformationUnitIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    FunctorIso (F2.coherentTransformationTotalMap F F (coherentIdentityTransformationVertex F) ≫
      F2.coherentDiagramTotalUnit F) (F2.coherentDiagramTotalUnit F) := by
  let x := coherentIdentityTransformationVertex F
  have e := (eqToIso (congrArg SSet.HomotopyCategory.mk
    (leftUnstraighteningMappingVertexMap_vertex F F x))) ≪≫
      (leftUnstraighteningMappingSpaceMap_edgeVertexIso F F
        (SSet.Edge.id (functorVertex F))).symm ≪≫ leftUnstraighteningEdgeMap_identityIso F
  have d := F2.smallUnstraighteningRelativeVertexIso F F
    (leftUnstraighteningMappingVertexMap F F x).property (Category.id_comp _) e
  have h := d.map
    (vertexFiberι ((ihom (smallLeftUnstraightening F)).map (smallLeftUnstraighteningProjection F))
      (functorVertex (smallLeftUnstraighteningProjection F)) ≫
        (ihom (smallLeftUnstraightening F)).map (F2.coherentDiagramTotalUnit F))
  change FunctorIso (F2.coherentTransformationTotalMap F F x ≫
    F2.coherentDiagramTotalUnit F)
    (smallLeftUnstraighteningOverMap F F (𝟙 _) ≫ F2.coherentDiagramTotalUnit F) at h
  have hi : smallLeftUnstraighteningOverMap F F (𝟙 _) =
      𝟙 (smallLeftUnstraightening F) := smallSimplicialMap_id _
  rw [hi, Category.id_comp] at h
  exact h

/-- 同じ元の合成三角形の長辺の作用は、指定単位の後で元の二辺の合成と同型。 -/
def coherentTransformationTriangleUnitIso {B : SSet.{u}}
    (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
    (T : F2.CoherentTransformationVertexTriangle F G J x y) :
    FunctorIso (F2.coherentTransformationTotalMap F J T.diagonal ≫
      F2.coherentDiagramTotalUnit J)
      (F2.coherentTransformationTotalMap F G x ≫
        F2.coherentTransformationTotalMap G J y ≫ F2.coherentDiagramTotalUnit J) := by
  exact (F2.coherentTransformationTriangleRelativeIso F G J x y T).map
    (vertexFiberι ((ihom (smallLeftUnstraightening F)).map (smallLeftUnstraighteningProjection J))
      (functorVertex (smallLeftUnstraighteningProjection F)) ≫
        (ihom (smallLeftUnstraightening F)).map (F2.coherentDiagramTotalUnit J))

end SerrePositivity.InfinityCategories.HomotopyLimits
