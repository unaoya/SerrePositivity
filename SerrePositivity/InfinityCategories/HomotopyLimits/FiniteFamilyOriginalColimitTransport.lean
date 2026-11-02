module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyOriginalKanComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProductNativeLegs
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanApexConeTransportLeg

/-!
概要：元の評価錐頂点の余極限を頂点に持つ全積錐を、同じ slice 比較辺で構成する。
方針：元の反復積の余極限全錐を、全脚と共有した同じ頂点比較の Kan 像で輸送する。
規約：元の底図式・頂点辺・全錐円柱を保持。底の quasicategory 性は不要。
使われ方：元の実際の評価脚の Kan 像を持つ積錐の極限性の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} [IsSiftedInfinity B] {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (c : JoinCone (finiteFamilyFunctorDiagram G)) (hc : IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hA : c.vertex = functorVertex A)

/-- 元の同じ頂点比較の Kan 像を、元の Kan 対象間の指定射に束ねる。 -/
def finiteFamilyConeApexKanObjectMap :
    F2.coherentDiagramTotalKanObject A ⟶
      F2.coherentDiagramTotalKanObject (finiteFamilyCoherentProduct G) :=
  finiteFamilyConeApexKanMap G c hc A hA

/-- 元の余極限積全錐を、全脚と同じ slice 代表から得た辺で頂点輸送する。 -/
def finiteFamilyOriginalColimitConeTransport :
    let Q := nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    F2.SpecifiedApexLimitConeTransport (finiteSiftedCoherentProductNativeCone Q.1 F)
      (SSet.yonedaEquiv.symm (coherentNerveVertex (F2.coherentDiagramTotalKanObject A)))
      (F2.edgeApexPrism (coherentNerveEdge (finiteFamilyConeApexKanObjectMap G c hc A hA))) := by
  let Q := nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  let a := finiteFamilyConeApexKanObjectMap G c hc A hA
  exact F2.specifiedApexLimitConeTransport _ (finiteSiftedCoherentProductNativeCone_isLimit Q.1 F)
    _ _ (F2.edgeApexPrism_zero _) (by
      rw [F2.edgeApexPrism_one]
      apply SSet.yonedaEquiv.injective
      exact (finiteSiftedCoherentProductNativeCone_vertex Q.1 F).symm)
    (fun x ↦ F2.edgeApexPrism_vertical_isInvertible _
      (coherentKanEdge_isInvertible_of_isQCatEquivalence
        (finiteFamilyConeApexKanMap_homotopyEquivalence G c hc A hA).isQCatEquivalence) x)

/-- 元の評価錐頂点の余極限 Kan 模型を頂点に持つ、元の図式上の全積錐。 -/
def finiteFamilyOriginalColimitTransportedCone :=
  (finiteFamilyOriginalColimitConeTransport G c hc A hA).cone

/-- 同じ元の比較辺で輸送した全積錐の頂点は、元の評価錐頂点の余極限。 -/
lemma finiteFamilyOriginalColimitTransportedCone_vertex :
    (finiteFamilyOriginalColimitTransportedCone G c hc A hA).vertex =
      coherentNerveVertex (F2.coherentDiagramTotalKanObject A) :=
  F2.kanApexConeTransport_vertex _ (finiteFamilyConeApexKanObjectMap G c hc A hA)
    (finiteFamilyOriginalColimitConeTransport G c hc A hA) rfl

/-- 同じ元の全図式を保つ輸送全錐は、元の評価錐頂点の余極限を頂点とする極限錐。 -/
lemma finiteFamilyOriginalColimitTransportedCone_isLimit :
    IsLimitCone (finiteFamilyOriginalColimitTransportedCone G c hc A hA) :=
  (finiteFamilyOriginalColimitConeTransport G c hc A hA).isLimit

end SerrePositivity.InfinityCategories.HomotopyLimits
