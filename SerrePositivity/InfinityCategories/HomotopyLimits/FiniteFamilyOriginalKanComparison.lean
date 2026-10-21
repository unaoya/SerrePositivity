module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyOriginalLegCocones
public import SerrePositivity.InfinityCategories.HomotopyLimits.TotalKanUnitComparisonReflection

/-!
概要：元の評価脚の Kan 像を、同じ slice 代表の頂点比較と反復射影の Kan 合成へ照合する。
方針：元の全錐の三角形と単位比較を、始域単位の弱同値から同じ Kan 射へ反映する。
規約：同じ元の全脚と頂点比較を保持。底の quasicategory 性は不要。
使われ方：元の全評価脚を持つ余極限の native 有限積錐の極限判定。
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
  (c : JoinCone (finiteFamilyFunctorDiagram G)) (hc : IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hA : c.vertex = functorVertex A)

/-- 全脚と同じ slice 代表を共有する、元の頂点比較の Kan 像。 -/
def finiteFamilyConeApexKanMap :=
  coherentTransformationTotalKanMap A (finiteFamilyCoherentProduct G)
    (finiteFamilyConeApexTransformation G c hc A hA)

/-- 同じ元の頂点比較の Kan 像は、任意の底上でホモトピー同値。 -/
lemma finiteFamilyConeApexKanMap_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (finiteFamilyConeApexKanMap G c hc A hA) :=
  coherentInvertibleTotalKanMap_homotopyEquivalence _ _ _
    (finiteFamilyConeApexTransformation_isInvertible G c hc A hA)

/-- 元の実際の評価脚の Kan 像は、同じ頂点比較と同じ反復射影の Kan 合成にホモトピック。 -/
lemma finiteFamilyOriginalLegKanMap_homotopy_indexed
    (i : Fin ((nonemptyFiniteIndexPresentation J).1 + 1)) :
    let Q := nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    Nonempty (SSet.Homotopy (finiteFamilyOriginalLegKanMap_indexed G c A hA i)
      (finiteFamilyConeApexKanMap G c hc A hA ≫
        F2.continuousKanReplacement.map (finiteCoherentSpaceProductTotalProjection Q.1 F i))) := by
  let Q := nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  let a := F2.coherentTransformationTotalMap A (finiteFamilyCoherentProduct G)
    (finiteFamilyConeApexTransformation G c hc A hA)
  have e : FunctorIso (F2.coherentTransformationTotalMap A (F i)
      (finiteFamilyOriginalLegTransformation G c A hA (Q.2.symm (ULift.up i))) ≫
        F2.coherentDiagramTotalUnit (F i))
      ((a ≫ finiteCoherentSpaceProductTotalProjection Q.1 F i) ≫
        F2.coherentDiagramTotalUnit (F i)) :=
    F2.functorIsoOfEq (finiteFamilyOriginalProjectionUnitIso_indexed G c hc A hA i)
      rfl (Category.assoc _ _ _).symm
  simpa only [finiteFamilyOriginalLegKanMap_indexed, finiteFamilyConeApexKanMap,
    coherentTransformationTotalKanMap, Q, F, a, Functor.map_comp] using
      coherentTotalKanMap_homotopy_of_unitIso A (F i) e

end SerrePositivity.InfinityCategories.HomotopyLimits
