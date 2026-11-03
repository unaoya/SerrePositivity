module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerCompositeVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantUnstraighteningValueVertex

/-!
概要：下面の三角形と指定区間輸送の二因子の三頂点を同じ実射の頂点へ揃える。
方針：元の相対三頂点の射影表示と指定 fiber 輸送の頂点式を使う。
規約：元の輸送を保持。使われ方：下面作用の指定因子を分離する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "z" => coherentDiagramTotalVertex G
local notation "v" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "q" => Iso.hom (constantUnstraighteningRelativeIso
  (leftUnstraighteningProjection F) z)
local notation "m" => CategoryTheory.Functor.map (ihom (leftUnstraightening F))
  (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))
local notation "I" => SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H)

/-- 下面の元の単位作用と第二辺の作用を、元の値へ射影した実際の合成射。 -/
def coherentColimitLowerCompositeAction :=
  ((leftUnstraighteningMappingVertexMap F (SSet.const (coherentDiagramTotalCocone F).vertex)
    (coherentVertexOfHomotopy (coconeTransformationHomotopy (coherentDiagramTotalCocone F)))).val ≫
    (leftUnstraighteningMappingVertexMap (SSet.const (coherentDiagramTotalCocone F).vertex)
      (SSet.const z)
        (coherentVertexOfHomotopy (coherentColimitIntervalConstantHomotopy B H))).val) ≫
    (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z ≫
      (pointedSpaceFiberValueEquivalence z).hom)

/-- 下面族比較の始点を値へ写すと、元の対角作用の頂点。 -/
lemma coherentColimitLowerFactor_source_vertex :
    (q ≫ m).app (Opposite.op ⦋0⦌)
      ((((SSet.const (coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H)) :
        (Δ[0] : SSet.{u + 1}) ⟶ _) ≫ leftUnstraighteningMappingSpaceMap F
          (SSet.const z)).app (Opposite.op ⦋0⦌) v)) =
      functorVertex (coherentColimitLowerAction B H) := by
  rw [coherentColimitLowerComposite_source_vertex, constantUnstraighteningRelativeIso_value_vertex]
  rfl

/-- 下面族比較と指定輸送比較の共有頂点は、同じ二作用の合成射の頂点。 -/
lemma coherentColimitLowerFactor_middle_vertex :
    (q ≫ m).app (Opposite.op ⦋0⦌)
      ((coconeIntervalRelativeComposite (coherentDiagramTotalCocone F) I).app
        (Opposite.op ⦋0⦌) v) = functorVertex (coherentColimitLowerCompositeAction B H) := by
  rw [coherentColimitLowerComposite_target_vertex, constantUnstraighteningRelativeIso_value_vertex]
  rfl

/-- 指定輸送比較の終点は、元の余錐 fiber 写像と同じ指定 fiber 輸送の合成の頂点。 -/
lemma coherentColimitLowerFactor_target_vertex :
    (m).app (Opposite.op ⦋0⦌)
      (((pointedIntervalTransport I).map ≫
        (pre (coconeFiberMap (coherentDiagramTotalCocone F))).app
          (vertexFiber pointedSpaceProjection z)).app (Opposite.op ⦋0⦌) v) =
      functorVertex (coconeFiberMap (coherentDiagramTotalCocone F) ≫
        coherentColimitFiberTransport B H ≫ (pointedSpaceFiberValueEquivalence z).hom) := by
  have et : functorVertex (coherentColimitFiberTransport B H) =
      (pointedIntervalTransport I).map.app (Opposite.op ⦋0⦌) v :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change (m).app _ (((pre (coconeFiberMap (coherentDiagramTotalCocone F))).app
    (vertexFiber pointedSpaceProjection z)).app _
      ((pointedIntervalTransport I).map.app _ v)) = _
  rw [← et]
  rfl

end SerrePositivity.InfinityCategories.F2
