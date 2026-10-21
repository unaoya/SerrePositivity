module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyTransportedLegComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiscreteNativeConeOfLegs
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeDiscreteLegHomotopy

/-!
概要：元の評価全錐の実際の全脚の Kan 像を持つ余極限全錐が、sifted な底で極限錐。
方針：元の全脚を変更せず native 錐を作り、同じ頂点で輸送した積錐との脚比較で判定する。
規約：元の全脚と余極限頂点を保持。底の quasicategory 性は不要。
使われ方：P_Σ の元の有限錐の像の極限性を元の全脚で回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (c : JoinCone (finiteFamilyFunctorDiagram G))
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hA : c.vertex = functorVertex A)

/-- 元の評価全脚の Kan 像をそのまま持つ、元の余極限頂点からの全錐。 -/
def finiteFamilyOriginalColimitNativeCone :
    let Q := nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    JoinCone (kanDiagramCoherentNerve
      (finiteKanProductDiagram Q.1 (fun k ↦ F2.coherentDiagramTotalKanObject (F k)))) :=
  let Q := nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  kanDiscreteNativeConeOfLegs
    (finiteKanProductDiagram Q.1 (fun k ↦ F2.coherentDiagramTotalKanObject (F k)))
    (F2.coherentDiagramTotalKanObject A)
    (fun i ↦ finiteFamilyOriginalLegKanMap_indexed G c A hA i.as.down)

/-- 元の全錐の頂点は、元の評価錐頂点の余極限 Kan 模型。 -/
lemma finiteFamilyOriginalColimitNativeCone_vertex :
    (finiteFamilyOriginalColimitNativeCone G c A hA).vertex =
      coherentNerveVertex (F2.coherentDiagramTotalKanObject A) :=
  kanDiscreteNativeConeOfLegs_vertex _ _ _

/-- 元の全錐の全脚は、元の実際の評価全脚の Kan 像そのもの。 -/
lemma finiteFamilyOriginalColimitNativeCone_kanLeg
    (i : Discrete (ULift.{u} (Fin ((nonemptyFiniteIndexPresentation J).1 + 1)))) :
    F2.kanNativeConeLeg (finiteFamilyOriginalColimitNativeCone G c A hA)
      (F2.coherentDiagramTotalKanObject A)
      (finiteFamilyOriginalColimitNativeCone_vertex G c A hA) i =
        finiteFamilyOriginalLegKanMap_indexed G c A hA i.as.down :=
  kanDiscreteNativeConeOfLegs_kanLeg _ _ _ i

/-- sifted な任意の底上で、元の全評価脚の Kan 像を持つ同じ全錐は極限錐。 -/
lemma finiteFamilyOriginalColimitNativeCone_isLimit [IsSiftedInfinity B] (hc : IsLimitCone c) :
    IsLimitCone (finiteFamilyOriginalColimitNativeCone G c A hA) := by
  apply (discreteSpaceCone_isLimit_iff_of_leg_homotopies _
    (finiteFamilyOriginalColimitNativeCone G c A hA)
    (finiteFamilyOriginalColimitTransportedCone G c hc A hA)
    (F2.coherentDiagramTotalKanObject A) (finiteFamilyOriginalColimitNativeCone_vertex G c A hA)
    (finiteFamilyOriginalColimitTransportedCone_vertex G c hc A hA) (fun i ↦ ?_)).mpr
      (finiteFamilyOriginalColimitTransportedCone_isLimit G c hc A hA)
  rw [finiteFamilyOriginalColimitNativeCone_kanLeg]
  exact Classical.choice (finiteFamilyOriginalLegKanMap_transported G c hc A hA i)

end SerrePositivity.InfinityCategories.HomotopyLimits
