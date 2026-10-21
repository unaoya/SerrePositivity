module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RealizedCoconeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTriangleFromHomClass
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransformationKanCocones

/-!
概要：元の変換と指定単位の合成を表す指定余錐を、同じ Kan 辺の全余錐作用へ照合する。
方針：同じ長辺の単位三角形と実現比較を用い、全余錐空間の充満忠実性で反映する。
規約：元の図式・変換・Kan 像・指定余錐を保持する。底の quasicategory 性は不要。
使われ方：実際の前層余極限脚を標準全評価 Kan 脚と比較する。
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
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (c : JoinCocone F) (hz : c.vertex = F2.coherentDiagramTotalVertex G)

/-- 同じ単位三角形の長辺を表す指定余錐は、同じ Kan 辺の全余錐作用と同型。 -/
def kanNativeCoconeIsoOfUnitTriangle
    (T : F2.CoherentTransformationUnitTriangle F G t)
    (e : VertexIso (coconeTransformationPointAt c hz) T.diagonal) :
    VertexIso (X := coconeMappingSpace F (F2.coherentDiagramTotalVertex G))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone F)
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint F G (coherentTransformationTotalKanMap F G t)))
      (F2.coconeMappingPointAt c (F2.coherentDiagramTotalVertex G) hz) := by
  let R := F2.coherentRepresentationCoconeRealization F (F2.coherentDiagramTotalVertex G)
    (F2.coherentTransformationTotalMap F G t ≫ F2.coherentDiagramTotalUnit G)
    (F2.coherentTransformationUnitRepresentation F G t T)
  exact coherentTransformationKanNativeUnitCoconeIso F G t T ≪≫
    (coconeRealizationComparisonIso T.diagonal R c hz e).symm

/-- 指定余錐の変換が元の変換と指定単位の合成類なら、同じ Kan 辺の作用と同型。 -/
def kanNativeCoconeIsoOfUnitHomClass
    (h : homMk (intervalMappingEdgeOfVertex t).toTruncated ≫
      homMk (intervalMappingEdgeOfVertex (F2.coherentTotalUnitRepresentation G).1).toTruncated =
        homMk (intervalMappingEdgeOfVertex (coconeTransformationPointAt c hz)).toTruncated) :
    VertexIso (X := coconeMappingSpace F (F2.coherentDiagramTotalVertex G))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone F)
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint F G (coherentTransformationTotalKanMap F G t)))
      (F2.coconeMappingPointAt c (F2.coherentDiagramTotalVertex G) hz) :=
  kanNativeCoconeIsoOfUnitTriangle F G t c hz
    (coherentTransformationTriangleOfHomClass t (F2.coherentTotalUnitRepresentation G).1
      (coconeTransformationPointAt c hz) h) (Iso.refl _)

end SerrePositivity.InfinityCategories.HomotopyLimits
