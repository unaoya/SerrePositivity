module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentProductComparisonEdge
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceBinaryTensorProduct
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.SpecifiedApexConeRestrictions

/-!
概要：coherent 積図式の元の余極限を頂点とする native な二項積錐を作る。
方針：同じ比較辺で標準積錐を輸送し、全錐の円柱とその二制限を保持する。
規約：底図式は元の二つの余極限頂点。使われ方：sifted 余極限の有限積保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} [IsSiftedInfinity B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の比較辺の全錐円柱を持つ、元の余極限頂点への指定輸送。 -/
def siftedCoherentProductNativeConeTransport :
    F2.SpecifiedApexLimitConeTransport
      (spaceBinaryTensorProductCone (F2.coherentDiagramTotalKanObject F)
        (F2.coherentDiagramTotalKanObject G))
      (SSet.yonedaEquiv.symm (F2.coherentDiagramTotalVertex (coherentSpaceTensorProduct F G)))
      (coherentProductComparisonApexPrism F G) :=
  F2.specifiedApexLimitConeTransport _ (spaceBinaryTensorProductCone_isLimit _ _) _ _
    (coherentProductComparisonApexPrism_zero F G) (by
      rw [coherentProductComparisonApexPrism_one]
      apply SSet.yonedaEquiv.injective
      exact (spaceBinaryTensorProductCone_vertex _ _).symm)
    (coherentProductComparisonApexPrism_vertical_isInvertible F G)

/-- 元の積図式の余極限頂点を持つ、二つの元の余極限の native な積錐。 -/
def siftedCoherentProductNativeCone : JoinCone (kanDiagramCoherentNerve
    (kanBinaryDiagram (F2.coherentDiagramTotalKanObject F) (F2.coherentDiagramTotalKanObject G))) :=
  (siftedCoherentProductNativeConeTransport F G).cone

/-- 同じ元の頂点と全錐を持つ二項積錐の普遍性。 -/
lemma siftedCoherentProductNativeCone_isLimit :
    IsLimitCone (siftedCoherentProductNativeCone F G) :=
  (siftedCoherentProductNativeConeTransport F G).isLimit

/-- 輸送した錐の頂点は、積図式の元の余極限頂点と厳密に一致する。 -/
lemma siftedCoherentProductNativeCone_vertex :
    (siftedCoherentProductNativeCone F G).vertex =
      F2.coherentDiagramTotalVertex (coherentSpaceTensorProduct F G) := by
  change SSet.yonedaEquiv (joinInl _ _ ≫ (siftedCoherentProductNativeCone F G).val) = _
  dsimp only [siftedCoherentProductNativeCone]
  rw [(siftedCoherentProductNativeConeTransport F G).apex_eq, Equiv.apply_symm_apply]

/-- 元の比較辺を頂点に持つ、標準積錐への全錐のホモトピー。 -/
def siftedCoherentProductNativeConeHomotopy :
    SSet.Homotopy (siftedCoherentProductNativeCone F G).val
      (spaceBinaryTensorProductCone (F2.coherentDiagramTotalKanObject F)
        (F2.coherentDiagramTotalKanObject G)).val :=
  (siftedCoherentProductNativeConeTransport F G).homotopy

/-- 全錐円柱の頂点への制限は、元の指定比較辺の円柱そのもの。 -/
lemma siftedCoherentProductNativeConeHomotopy_apex :
    (joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫
      (siftedCoherentProductNativeConeHomotopy F G).h =
        (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
          coherentProductComparisonApexPrism F G :=
  (siftedCoherentProductNativeConeTransport F G).apex

/-- 全錐円柱は、二つの元の余極限頂点の底図式を全時刻で固定する。 -/
lemma siftedCoherentProductNativeConeHomotopy_diagram :
    (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫
      (siftedCoherentProductNativeConeHomotopy F G).h =
        fst _ (Δ[1] : SSet.{u + 1}) ≫ kanDiagramCoherentNerve
          (kanBinaryDiagram (F2.coherentDiagramTotalKanObject F)
            (F2.coherentDiagramTotalKanObject G)) :=
  (siftedCoherentProductNativeConeTransport F G).diagram

end SerrePositivity.InfinityCategories.HomotopyLimits
