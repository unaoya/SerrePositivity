module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyOriginalProjectionUnit
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransformationKanCocones

/-!
概要：元の評価全脚の Kan 像の全余錐作用を、頂点比較と元の反復射影の余錐へ移す。
方針：同じ native 辺の単位表示・元の全空間写像余錐・指定単位後の比較を続ける。
規約：元の全脚と同じ有限表示を保持。底の quasicategory 性は要求しない。
使われ方：元の P_Σ 評価錐の脚と、sifted な余極限積錐の全脚の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (c : JoinCone (finiteFamilyFunctorDiagram G)) (hc : IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hA : c.vertex = functorVertex A)

/-- 元の実際の各評価脚の全空間作用の、元の余極限模型間の Kan 像。 -/
def finiteFamilyOriginalLegKanMap_indexed
    (i : Fin ((nonemptyFiniteIndexPresentation J).1 + 1)) :=
  let Q := nonemptyFiniteIndexPresentation J
  coherentTransformationTotalKanMap A (G (Q.2.symm (ULift.up i)))
    (finiteFamilyOriginalLegTransformation G c A hA (Q.2.symm (ULift.up i)))

/-- 元の各評価脚の全余錐作用は、元の頂点比較と同じ反復射影の全余錐へ移る。 -/
def finiteFamilyOriginalLegNativeProjectionCoconeIso_indexed
    (i : Fin ((nonemptyFiniteIndexPresentation J).1 + 1)) :
    let Q := nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    let m := F2.coherentTransformationTotalMap A (finiteFamilyCoherentProduct G)
      (finiteFamilyConeApexTransformation G c hc A hA) ≫
        finiteCoherentSpaceProductTotalProjection Q.1 F i
    VertexIso (X := coconeMappingSpace A (F2.coherentDiagramTotalVertex (F i)))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone A)
        (F2.coherentDiagramTotalVertex (F i))).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint A (F i) (finiteFamilyOriginalLegKanMap_indexed G c A hA i)))
      (F2.coconeMappingPointAt (F2.coherentTotalMapCocone A (F i) m)
        (F2.coherentDiagramTotalVertex (F i)) (F2.coherentTotalMapCocone_vertex A (F i) m)) := by
  let Q := nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  let t := finiteFamilyOriginalLegTransformation G c A hA (Q.2.symm (ULift.up i))
  let a := F2.coherentTransformationTotalMap A (finiteFamilyCoherentProduct G)
    (finiteFamilyConeApexTransformation G c hc A hA)
  let m := a ≫ finiteCoherentSpaceProductTotalProjection Q.1 F i
  have e : FunctorIso (F2.coherentTransformationTotalMap A (F i) t ≫
      F2.coherentDiagramTotalUnit (F i)) (m ≫ F2.coherentDiagramTotalUnit (F i)) :=
    F2.functorIsoOfEq (finiteFamilyOriginalProjectionUnitIso_indexed G c hc A hA i)
      rfl (Category.assoc _ _ _).symm
  exact coherentTransformationTotalKanNativeCoconeIso A (F i) t ≪≫
    totalKanMapCoconeIso A (F i) (F2.coherentTransformationTotalMap A (F i) t)
      (SSet.RelativeMorphism.Homotopy.refl _) ≪≫
        constantCoconeHomotopyIso A (F2.coherentDiagramTotalVertex (F i)) e.simplicialHomotopy

end SerrePositivity.InfinityCategories.HomotopyLimits
