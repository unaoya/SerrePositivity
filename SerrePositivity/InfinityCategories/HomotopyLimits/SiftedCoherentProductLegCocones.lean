module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedCoherentProductNativeLegs
public import SerrePositivity.InfinityCategories.HomotopyLimits.TotalKanMapCocone
public import SerrePositivity.InfinityCategories.F2.CoherentTransformationUnitCocone

/-!
概要：native 積の両 Kan 脚の単位表現を、元の射影変換と単位の合成余錐へ比較する。
方針：同じ脚の Kan ホモトピーを余錐空間へ反映し、指定合成三角形の比較を続ける。
規約：余錐全体と元の三角形を保持。使われ方：sifted 余極限の積比較の余錐側の界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} [IsSiftedInfinity B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の native 積の第一 Kan 脚の単位表現を実現した、積図式上の余錐。 -/
def siftedCoherentProductLeftLegCocone : JoinCocone (coherentSpaceTensorProduct F G) :=
  totalKanMapCocone (coherentSpaceTensorProduct F G) F
    (siftedCoherentProductNativeKanLeg F G ⟨⟨true⟩⟩)

/-- 第一脚の単位表現の余錐は、第一図式の元の余極限頂点を持つ。 -/
lemma siftedCoherentProductLeftLegCocone_vertex :
    (siftedCoherentProductLeftLegCocone F G).vertex = F2.coherentDiagramTotalVertex F :=
  totalKanMapCocone_vertex _ _ _

/-- 第一脚の単位表現の全余錐は、元の射影変換と単位の任意の指定合成三角形の余錐と同型。 -/
def siftedCoherentProductLeftLegCoconeIso
    (T : F2.CoherentTransformationUnitTriangle (coherentSpaceTensorProduct F G) F
      (coherentSpaceTensorProductFstVertex F G)) :
    VertexIso (X := coconeMappingSpace (coherentSpaceTensorProduct F G)
      (F2.coherentDiagramTotalVertex F))
      (F2.coconeMappingPointAt (siftedCoherentProductLeftLegCocone F G)
        (F2.coherentDiagramTotalVertex F) (siftedCoherentProductLeftLegCocone_vertex F G))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone
        (coherentSpaceTensorProduct F G) F (coherentSpaceTensorProductFstVertex F G) T)
        (F2.coherentDiagramTotalVertex F) (F2.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  totalKanMapCoconeIso (coherentSpaceTensorProduct F G) F
    (coherentSpaceTensorProductTotalFst F G)
    (Classical.choice (siftedCoherentProductNativeKanLeg_left F G)) ≪≫
      (F2.coherentTransformationUnitCoconeIso (coherentSpaceTensorProduct F G) F
        (coherentSpaceTensorProductFstVertex F G) T).symm

/-- 元の native 積の第二 Kan 脚の単位表現を実現した、積図式上の余錐。 -/
def siftedCoherentProductRightLegCocone : JoinCocone (coherentSpaceTensorProduct F G) :=
  totalKanMapCocone (coherentSpaceTensorProduct F G) G
    (siftedCoherentProductNativeKanLeg F G ⟨⟨false⟩⟩)

/-- 第二脚の単位表現の余錐は、第二図式の元の余極限頂点を持つ。 -/
lemma siftedCoherentProductRightLegCocone_vertex :
    (siftedCoherentProductRightLegCocone F G).vertex = F2.coherentDiagramTotalVertex G :=
  totalKanMapCocone_vertex _ _ _

/-- 第二脚の単位表現の全余錐も、元の射影変換と単位の任意の指定合成三角形の余錐と同型。 -/
def siftedCoherentProductRightLegCoconeIso
    (T : F2.CoherentTransformationUnitTriangle (coherentSpaceTensorProduct F G) G
      (coherentSpaceTensorProductSndVertex F G)) :
    VertexIso (X := coconeMappingSpace (coherentSpaceTensorProduct F G)
      (F2.coherentDiagramTotalVertex G))
      (F2.coconeMappingPointAt (siftedCoherentProductRightLegCocone F G)
        (F2.coherentDiagramTotalVertex G) (siftedCoherentProductRightLegCocone_vertex F G))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone
        (coherentSpaceTensorProduct F G) G (coherentSpaceTensorProductSndVertex F G) T)
        (F2.coherentDiagramTotalVertex G) (F2.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  totalKanMapCoconeIso (coherentSpaceTensorProduct F G) G
    (coherentSpaceTensorProductTotalSnd F G)
    (Classical.choice (siftedCoherentProductNativeKanLeg_right F G)) ≪≫
      (F2.coherentTransformationUnitCoconeIso (coherentSpaceTensorProduct F G) G
        (coherentSpaceTensorProductSndVertex F G) T).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
