module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyProductLegReadback

/-!
概要：元の評価全錐の実際の脚を、元の頂点比較と反復全空間射影の単位表現へ移す。
方針：同じ全錐の合成三角形の比較に、元の積脚の厳密な読み戻しと単位比較を続ける。
規約：元の全脚・有限表示・指定単位を保持。底の quasicategory 性は不要。
使われ方：元の評価全脚の native 余極限作用と、sifted 積錐の元の全脚の比較。
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

/-- 元の実際の評価脚は、元の単位の後で頂点比較と同じ反復全空間射影の合成に同型。 -/
def finiteFamilyOriginalProjectionUnitIso_indexed
    (i : Fin ((nonemptyFiniteIndexPresentation J).1 + 1)) :
    let Q := nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    FunctorIso (F2.coherentTransformationTotalMap A (F i)
      (finiteFamilyOriginalLegTransformation G c A hA (Q.2.symm (ULift.up i))) ≫
        F2.coherentDiagramTotalUnit (F i))
      (F2.coherentTransformationTotalMap A (finiteFamilyCoherentProduct G)
        (finiteFamilyConeApexTransformation G c hc A hA) ≫
      finiteCoherentSpaceProductTotalProjection Q.1 F i ≫ F2.coherentDiagramTotalUnit (F i)) := by
  let Q := nonemptyFiniteIndexPresentation J
  exact finiteFamilyOriginalLegUnitIso G c hc A hA (Q.2.symm (ULift.up i)) ≪≫
    (finiteFamilyProductLegUnitIso_indexed G i).precomp
      (F2.coherentTransformationTotalMap A (finiteFamilyCoherentProduct G)
        (finiteFamilyConeApexTransformation G c hc A hA))

end SerrePositivity.InfinityCategories.HomotopyLimits
