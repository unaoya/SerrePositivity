module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentInvertibleTotalKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.CoherentTransformationUnitCocone

/-!
概要：元の coherent 変換の Kan 像による全余錐作用を、指定単位三角形へ照合する。
方針：元の Kan 射の単位表示・元の全空間写像余錐・同じ合成三角形の比較を続ける。
規約：元の辺・変換・全余錐・指定三角形を保持。可逆性や底の充填性は不要。
使われ方：P_Σ の元の全錐比較を、余極限の全脚へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (T : F2.CoherentTransformationUnitTriangle F G t)

/-- 元の同じ Kan 像の単位表現の余錐は、指定単位三角形の元の余錐に同型。 -/
def coherentTransformationKanUnitCoconeIso :
    VertexIso (X := coconeMappingSpace F (F2.coherentDiagramTotalVertex G))
      (F2.coconeMappingPointAt
        (totalKanMapCocone F G (coherentTransformationTotalKanMap F G t))
        (F2.coherentDiagramTotalVertex G) (totalKanMapCocone_vertex _ _ _))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone F G t T)
        (F2.coherentDiagramTotalVertex G)
        (F2.coherentTransformationUnitCocone_vertex F G t T)) :=
  totalKanMapCoconeIso F G (F2.coherentTransformationTotalMap F G t)
    (SSet.RelativeMorphism.Homotopy.refl _) ≪≫
      (F2.coherentTransformationUnitCoconeIso F G t T).symm

/-- 元の同じ Kan 比較辺の全余錐作用は、元の変換と指定単位の全三角形へ移る。 -/
def coherentTransformationKanNativeUnitCoconeIso :
    VertexIso (X := coconeMappingSpace F (F2.coherentDiagramTotalVertex G))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone F)
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint F G (coherentTransformationTotalKanMap F G t)))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone F G t T)
        (F2.coherentDiagramTotalVertex G)
        (F2.coherentTransformationUnitCocone_vertex F G t T)) :=
  coherentTransformationTotalKanNativeCoconeIso F G t ≪≫
    coherentTransformationKanUnitCoconeIso F G t T

end SerrePositivity.InfinityCategories.HomotopyLimits
