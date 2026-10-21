module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TotalKanNativeHomAction

/-!
概要：元の Kan 射の coherent 辺による native 余錐作用は、元の単位表現の余錐と同型。
方針：同じ左 Hom の点で全輸送比較を評価し、元の標準余錐比較の充満忠実性で反映する。
規約：元の余極限余錐・辺・単位を保持。使われ方：sifted 積の脚の全余錐の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : F2.coherentDiagramTotalKan F ⟶ F2.coherentDiagramTotalKan G)

/-- 同じ元の coherent 辺の native な余錐作用と、同じ Kan 射の単位表現の全余錐は同型。 -/
def totalKanNativeCoconeIso :
    VertexIso (X := coconeMappingSpace F (F2.coherentDiagramTotalVertex G))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone F)
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint F G a))
      (F2.coconeMappingPointAt (totalKanMapCocone F G a) (F2.coherentDiagramTotalVertex G)
        (totalKanMapCocone_vertex F G a)) := by
  let c := F2.coherentDiagramTotalCocone F
  let z := F2.coherentDiagramTotalVertex G
  let q := F2.coconeMappingPointAt (totalKanMapCocone F G a) z (totalKanMapCocone_vertex F G a)
  let D := F2.coherentCoconeTotalComparison F z ≫
    (F2.smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv
  have hd : IsQCatEquivalence D :=
    (F2.coherentCoconeTotalComparison_isQCatEquivalence F z).comp
      ((qCatEquivalenceOfIso
        (F2.smallUnstraighteningHomIso F (spaceInfinityObject z).obj).symm).isQCatEquivalence)
  apply hd.isFullyFaithful.preimageVertexIso
  have h := ((F2.coherentCoconeTransportActionIso F c z).app (totalKanNativeHomPoint F G a)) ≪≫
    totalKanNativeHomActionIso F G a
  have hq : D.app (Opposite.op ⦋0⦌) q =
      functorVertex (F2.coconeFiberValueMapAt (totalKanMapCocone F G a) z
        (totalKanMapCocone_vertex F G a)) :=
    F2.coconeFiberValueMapAt_smallComparison F (totalKanMapCocone F G a) z
      (totalKanMapCocone_vertex F G a)
  change VertexIso (D.app _ ((coconePointHomFamily c z).app _ (totalKanNativeHomPoint F G a)))
    (D.app _ q)
  rw [hq]
  exact h ≪≫ (F2.coherentConstantCoconeFiberIso F z (totalKanMapCoconeInput F G a)).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
