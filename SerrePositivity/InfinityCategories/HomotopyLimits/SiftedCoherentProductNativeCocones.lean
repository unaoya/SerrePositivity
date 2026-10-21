module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TotalKanNativeCoconeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedCoherentProductLegCocones

/-!
概要：native な積の元の両脚の余錐作用を、元の射影変換と単位の合成余錐へ同定する。
方針：同じ脚の全一単体を左 Hom に保ち、完成済みの単位表現との比較を合成する。
規約：元の余極限余錐・積錐・射影変換・指定三角形を保持。
使われ方：coherent な sifted 余極限の native な積比較の完成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} [IsSiftedInfinity B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 左 Hom で使う第一辺は、元の native 積錐の第一脚の全一単体そのもの。 -/
lemma siftedCoherentProductLeftNativeEdge :
    (totalKanNativeEdge (coherentSpaceTensorProduct F G) F
      (siftedCoherentProductNativeKanLeg F G ⟨⟨true⟩⟩)).edge =
        (F2.nativeConeLeg (siftedCoherentProductNativeCone F G)
          (ULift.up (ComposableArrows.mk₀ ⟨⟨true⟩⟩))).edge :=
  F2.kanNativeConeLeg_edge _ _ _ _

/-- 左 Hom で使う第二辺も、元の native 積錐の第二脚の全一単体そのもの。 -/
lemma siftedCoherentProductRightNativeEdge :
    (totalKanNativeEdge (coherentSpaceTensorProduct F G) G
      (siftedCoherentProductNativeKanLeg F G ⟨⟨false⟩⟩)).edge =
        (F2.nativeConeLeg (siftedCoherentProductNativeCone F G)
          (ULift.up (ComposableArrows.mk₀ ⟨⟨false⟩⟩))).edge :=
  F2.kanNativeConeLeg_edge _ _ _ _

/-- 元の native 第一脚が元の余極限余錐に作用した全余錐は、指定射影と単位の余錐と同型。 -/
def siftedCoherentProductLeftNativeCoconeIso
    (T : F2.CoherentTransformationUnitTriangle (coherentSpaceTensorProduct F G) F
      (coherentSpaceTensorProductFstVertex F G)) :
    VertexIso (X := coconeMappingSpace (coherentSpaceTensorProduct F G)
      (F2.coherentDiagramTotalVertex F))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone (coherentSpaceTensorProduct F G))
        (F2.coherentDiagramTotalVertex F)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint (coherentSpaceTensorProduct F G) F
            (siftedCoherentProductNativeKanLeg F G ⟨⟨true⟩⟩)))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone
        (coherentSpaceTensorProduct F G) F (coherentSpaceTensorProductFstVertex F G) T)
        (F2.coherentDiagramTotalVertex F) (F2.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  totalKanNativeCoconeIso (coherentSpaceTensorProduct F G) F
    (siftedCoherentProductNativeKanLeg F G ⟨⟨true⟩⟩) ≪≫
      siftedCoherentProductLeftLegCoconeIso F G T

/-- 元の native 第二脚の全余錐作用も、指定第二射影と元の単位の合成余錐と同型。 -/
def siftedCoherentProductRightNativeCoconeIso
    (T : F2.CoherentTransformationUnitTriangle (coherentSpaceTensorProduct F G) G
      (coherentSpaceTensorProductSndVertex F G)) :
    VertexIso (X := coconeMappingSpace (coherentSpaceTensorProduct F G)
      (F2.coherentDiagramTotalVertex G))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone (coherentSpaceTensorProduct F G))
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint (coherentSpaceTensorProduct F G) G
            (siftedCoherentProductNativeKanLeg F G ⟨⟨false⟩⟩)))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone
        (coherentSpaceTensorProduct F G) G (coherentSpaceTensorProductSndVertex F G) T)
        (F2.coherentDiagramTotalVertex G) (F2.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  totalKanNativeCoconeIso (coherentSpaceTensorProduct F G) G
    (siftedCoherentProductNativeKanLeg F G ⟨⟨false⟩⟩) ≪≫
      siftedCoherentProductRightLegCoconeIso F G T

end SerrePositivity.InfinityCategories.HomotopyLimits
