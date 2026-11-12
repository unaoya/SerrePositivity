module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalVertex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeUnitRepresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalFiberTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningTriangleComposition

/-!
概要：元の単位正方形の下三角形の全空間作用を、同じ指定辺の普遍輸送へ比較する。
方針：元の三辺と二単体を合成比較へ入力し、定値図式の全族の輸送比較へ続ける。
規約：元の対角・単位・余極限の指定辺を保持。使われ方：a6 の native 辺との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の native 余錐の単位を円柱から coherent 頂点へ戻すと、元の単位頂点。 -/
lemma coherentVertexOfHomotopy_cocone {K : SSet.{u + 1}} {F : K ⟶ SpaceInfinity.{u}}
    (c : JoinCocone F) : coherentVertexOfHomotopy (coconeTransformationHomotopy c) =
      coconeTransformationVertex c :=
  coherentVertexOfHomotopy_of_vertex _

variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の下二単体の長変換の全作用は、元の単位と指定区間による実際の相対合成。 -/
def coherentColimitLowerCompositeIso : FunctorIso
    ((SSet.const (coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H)) :
      (Δ[0] : SSet.{u + 1}) ⟶ _) ≫
      leftUnstraighteningMappingSpaceMap F (SSet.const (coherentDiagramTotalVertex G)))
    (coconeIntervalRelativeComposite (coherentDiagramTotalCocone F)
      (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))) := by
  let T := coherentTriangleOfFunctorTriangle (coherentColimitTargetLowerTriangle B H)
  refine unstraighteningMappingTriangleIso F
    (SSet.const (coherentDiagramTotalCocone F).vertex)
    (SSet.const (coherentDiagramTotalVertex G))
    (SSet.const (coconeTransformationVertex (coherentDiagramTotalCocone F)))
    (constantDiagramTransformation ((SSet.uliftFunctor.{u + 1, u}).obj B)
      (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H)))
    (SSet.const T.diagonal) T.diagram ?_ ?_ T.long
  · exact T.first.trans (congrArg (fun t =>
      coherentTransformationFamilyDiagram (SSet.const t))
        (coherentVertexOfHomotopy_cocone (coherentDiagramTotalCocone F)))
  · have h := coherentColimitIntervalVertex_constant B H
    rw [SSet.yonedaEquiv_symm_zero] at h
    exact T.second.trans (congrArg coherentTransformationFamilyDiagram h.symm)

/-- 元の対角の全作用は、元の指定余極限辺による fiber 輸送と単位の前合成に同型。 -/
def coherentColimitLowerFiberHomIso : FunctorIso
    (((SSet.const (coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H)) :
      (Δ[0] : SSet.{u + 1}) ⟶ _) ≫
      leftUnstraighteningMappingSpaceMap F (SSet.const (coherentDiagramTotalVertex G))) ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F)
        (coherentDiagramTotalVertex G)).hom)
    ((pointedIntervalTransport
      (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))).map ≫
      (pre (coconeFiberMap (coherentDiagramTotalCocone F))).app
        (vertexFiber pointedSpaceProjection (coherentDiagramTotalVertex G))) :=
  ((coherentColimitLowerCompositeIso B H).postcomp
    (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F)
      (coherentDiagramTotalVertex G)).hom) ≪≫
    coconeIntervalFiberHomIso (coherentDiagramTotalCocone F)
      (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))

end SerrePositivity.InfinityCategories.F2
