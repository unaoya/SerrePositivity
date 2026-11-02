module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanApexConeTransportLeg
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanNativeConeLeg
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedInfinity
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteCoherentProductNativeCone
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteCoherentProductNativeLegs
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProductTotalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyFunctorProduct
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteFamilyOriginalColimitTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyOriginalKanComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyOriginalLegCocones
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyProductCone
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteKanProductNative

/-!
概要：同じ元の頂点比較で輸送した余極限積錐の全脚を、元の評価脚の Kan 像へ照合する。
方針：元の輸送全錐円柱の脚比較と、元の反復射影・評価脚の Kan ホモトピーを続ける。
規約：同じ全錐・頂点・全脚を保持し、底の quasicategory 性は不要。
使われ方：元の実際の評価脚の Kan 像を持つ有限全錐の極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} [IsSiftedInfinity B] {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (c : JoinCone (finiteFamilyFunctorDiagram G)) (hc : IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hA : c.vertex = functorVertex A)

/-- 同じ元の全錐円柱で輸送した全脚を、元の頂点の余極限 Kan 対象の射へ戻す。 -/
def finiteFamilyTransportedColimitKanLeg
    (i : Discrete (ULift.{u} (Fin ((nonemptyFiniteIndexPresentation J).1 + 1)))) :=
  F2.kanNativeConeLeg (finiteFamilyOriginalColimitTransportedCone G c hc A hA)
    (F2.coherentDiagramTotalKanObject A)
    (finiteFamilyOriginalColimitTransportedCone_vertex G c hc A hA) i

/-- 同じ輸送脚は、元の頂点比較と元の反復全空間射影の Kan 合成にホモトピック。 -/
lemma finiteFamilyTransportedColimitKanLeg_projection
    (i : Discrete (ULift.{u} (Fin ((nonemptyFiniteIndexPresentation J).1 + 1)))) :
    let Q := nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    Nonempty (SSet.Homotopy (finiteFamilyTransportedColimitKanLeg G c hc A hA i)
      (finiteFamilyConeApexKanMap G c hc A hA ≫ F2.continuousKanReplacement.map
        (finiteCoherentSpaceProductTotalProjection Q.1 F i.as.down))) := by
  let Q := nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  let a := finiteFamilyConeApexKanObjectMap G c hc A hA
  have h := F2.kanApexConeTransportLeg_comparison
    (finiteSiftedCoherentProductNativeCone Q.1 F) a
    (finiteFamilyOriginalColimitConeTransport G c hc A hA) rfl
    (finiteSiftedCoherentProductNativeCone_vertex Q.1 F) i
  have k := functorHomotopyPrecomp
    (Classical.choice (finiteSiftedCoherentProductNativeKanLeg_projection Q.1 F i)) a
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).mpr h).trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨k⟩)

/-- 元の実際の全評価脚の Kan 像は、同じ輸送極限錐の全脚にホモトピック。 -/
lemma finiteFamilyOriginalLegKanMap_transported
    (i : Discrete (ULift.{u} (Fin ((nonemptyFiniteIndexPresentation J).1 + 1)))) :
    Nonempty (SSet.Homotopy (finiteFamilyOriginalLegKanMap_indexed G c A hA i.as.down)
      (finiteFamilyTransportedColimitKanLeg G c hc A hA i)) := by
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).mpr
    (finiteFamilyOriginalLegKanMap_homotopy_indexed G c hc A hA i.as.down)).trans
      ((functorVertex_piZero_eq_iff_homotopy _ _).mpr
        (finiteFamilyTransportedColimitKanLeg_projection G c hc A hA i)).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
