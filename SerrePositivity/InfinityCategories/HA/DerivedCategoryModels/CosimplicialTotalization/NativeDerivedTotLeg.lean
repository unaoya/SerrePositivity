module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedTotCone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeStandardLeg
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeLegPostcomposition

/-!
概要：同じTot錐を既存D(A)へ移した脚は、元の第0頂点の標準脚の像そのもの。
方針：元のjoin錐の後合成の一次単体の式に、C01の厳密等式を代入する。
規約：IS-W2 C04。元の頂点と脚、全join射の同じ後合成を使う。
使われ方：HA 1.2.4、元のstrict図式への指定導来Tot錐。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元の同じ第0頂点の標準脚は、指定された出力分解の同じ一次単体で写る。 -/
theorem nativeDerivedCone_standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (derivedConeLeg (nativeDerivedCone X) (ULift.up (nerveVertex (AsSmall.up.obj n)))).edge =
      (SerrePositivity.EInfinity.ComplexLimits.complexSemifreeResolutionInfinity A).app
        (Opposite.op ⦋1⦌)
        (dgClosedEdge A (Complex A)
          ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map
            (standardLeg A X n))).edge := by
  rw [nativeDerivedCone, derivedConeLeg_mapJoinCone, nativeDGCone_standardLeg]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
