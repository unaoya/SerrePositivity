module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCoconeIntervalTransportAction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCoconeValuePre
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FullyFaithfulVertexIsoImage

/-!
概要：元の全空間余錐の普遍区間作用は、指定区間比較の等式を反映する。
方針：元の値への後合成同値と fiber 前合成同値を自然性で交換する。
規約：全 Hom と元の射を保持。使われ方：三角形比較の像の一致から指定値を回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (z : SpaceInfinity.{u} _⦋0⦌)

/-- 同じ元の fiber 前合成と値への後合成の全作用は同値。 -/
lemma coherentCoconeFiberValueAction_isQCatEquivalence :
    IsQCatEquivalence (coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F) z) := by
  have hp := (coherentTotalCoconeFiber_value_pre_homotopyEquivalence F
    (spaceInfinityObject z).obj).isQCatEquivalence
  have hv := (pointedSpaceFiberValueEquivalence z).isQCatEquivalence.postcompose
    (vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex)
  have h := hv.comp hp
  rw [(pre (coconeFiberMap (coherentDiagramTotalCocone F))).naturality] at h
  exact h

/-- 元の全区間族の普遍作用は、元の全空間余錐について同値。 -/
lemma coherentCoconeIntervalTransportAction_isQCatEquivalence :
    IsQCatEquivalence
      (coherentCoconeIntervalTransportAction F (coherentDiagramTotalCocone F) z) := by
  exact (parametrizedPointedSpaceTransport_isQCatEquivalence
    (coherentDiagramTotalCocone F).vertex z).comp
      (coherentCoconeFiberValueAction_isQCatEquivalence F z)

/-- 元の同じ区間両端間の比較は、元の普遍作用による像の一致から値まで一致する。 -/
lemma coherentCoconeIntervalTransportAction_iso_injective
    {x y : (intervalMappingSpace (coherentDiagramTotalCocone F).vertex z) _⦋0⦌} :
    Function.Injective (fun e : VertexIso x y => VertexIso.map e
      (coherentCoconeIntervalTransportAction F (coherentDiagramTotalCocone F) z)) := by
  exact vertexIso_map_injective
    (coherentCoconeIntervalTransportAction_isQCatEquivalence F z).isFullyFaithful

end SerrePositivity.InfinityCategories.F2
