module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalIsoHomClass
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanNativeCoconeUnitCriterion

/-!
概要：標準 native 余錐の元の変換を、選択済み全空間単位の同じ Hom 類へ照合する。
方針：元の全空間余錐の実現比較を区間同型へ移し、同じ回収辺の類を反映する。
規約：元の標準余錐・単位表現・Kan 辺の作用を保持する。
使われ方：実際の脚の標準単位正方形から全余錐作用への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の全空間余錐の標準変換は、選択済みの同じ単位表現と区間内で同型。 -/
def nativeTotalUnitTransformationIso :
    VertexIso (coconeTransformationPointAt (F2.coherentDiagramTotalCocone F)
      (F2.coherentDiagramTotalCocone_vertex F)) (F2.coherentTotalUnitRepresentation F).1 :=
  realizedCoconeTransformationIso (F2.coherentTotalUnitRepresentation F).1
    (F2.coherentTotalCoconeRealization F)

/-- 元の標準 native 余錐変換と選択済み単位から回収した辺は、同じ Hom 類。 -/
lemma nativeTotalUnitTransformation_homMk :
    homMk (intervalMappingEdgeOfVertex (coconeTransformationPointAt
      (F2.coherentDiagramTotalCocone F) (F2.coherentDiagramTotalCocone_vertex F))).toTruncated =
    homMk (intervalMappingEdgeOfVertex (F2.coherentTotalUnitRepresentation F).1).toTruncated :=
  intervalRecoveredHom_eq_of_vertexIso (nativeTotalUnitTransformationIso F)

/-- 元の native 標準単位との合成類から、同じ Kan 辺と指定余錐の全作用を比較。 -/
def kanNativeCoconeIsoOfNativeUnitHomClass
    (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (c : JoinCocone F) (hz : c.vertex = F2.coherentDiagramTotalVertex G)
    (h : homMk (intervalMappingEdgeOfVertex t).toTruncated ≫
      homMk (intervalMappingEdgeOfVertex (coconeTransformationPointAt
        (F2.coherentDiagramTotalCocone G) (F2.coherentDiagramTotalCocone_vertex G))).toTruncated =
      homMk (intervalMappingEdgeOfVertex (coconeTransformationPointAt c hz)).toTruncated) :
    VertexIso (X := coconeMappingSpace F (F2.coherentDiagramTotalVertex G))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone F)
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint F G (coherentTransformationTotalKanMap F G t)))
      (F2.coconeMappingPointAt c (F2.coherentDiagramTotalVertex G) hz) := by
  apply kanNativeCoconeIsoOfUnitHomClass F G t c hz
  rw [nativeTotalUnitTransformation_homMk G] at h
  exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
