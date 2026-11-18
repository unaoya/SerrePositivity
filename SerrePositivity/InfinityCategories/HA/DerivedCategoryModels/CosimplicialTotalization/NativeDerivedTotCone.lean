module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeLimit
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SemifreeRingEvaluationEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedLimitTransfer

/-!
概要：元のTot錐を同じ半自由出力分解で既存D(A)へ移し、極限性と頂点を保つ。
方針：定数一点係数の準同値、既存の出力分解の全錐判定、同じ評価の同値を合成する。
規約：IS-W2 C02・C03。元の全join射を後合成する。Reedy条件や模型圏仮定を追加しない。
使われ方：HA 1.2.4、元のstrict余単体図式とnativeな導来極限の指定錐。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元のdg図式を同じ半自由出力分解で既存D(A)へ送った全図式。 -/
def nativeDerivedDiagram (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      derivedInfinityCategory A :=
  nativeDGDiagram X ≫ _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A

/-- 元のTot錐の同じ全join射を、同じ出力分解で既存D(A)へ送る。 -/
def nativeDerivedCone (X : CosimplicialObject (Complex A)) : JoinCone (nativeDerivedDiagram X) :=
  mapJoinCone (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A) (nativeDGCone X)

/-- 同じTot錐の出力分解の像は、既存D(A)でnative極限錐である。 -/
theorem nativeDerivedCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeDerivedCone X) := by
  have hraw := (dgNerve_map_isQCatEquivalence_of_quasiEquivalence (ringConstantDG A)
    (ringConstantDG_quasiEquivalence A)).isLimitCone_iff (nativeDGCone X) |>.mp
      (nativeDGCone_isLimit X)
  have hr := dgModuleResolvedInfinity_isLimitCone_of_raw A (Complex A) PUnit.{1}
    (ringConstantDG A) (nativeDGCone X) hraw
  have h := (semifreeRingEvaluationInfinity_isQCatEquivalence A).isLimitCone_iff
    (mapJoinCone (dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A))
      (nativeDGCone X)) |>.mp hr
  simpa only [nativeDerivedCone, _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity, mapJoinCone,
    Category.assoc] using h

/-- 移した錐の頂点は、元の積Totの同じ指定半自由分解の頂点。 -/
theorem nativeDerivedCone_vertex (X : CosimplicialObject (Complex A)) :
    (nativeDerivedCone X).vertex =
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
        (Simplex.vertex ((productTotalFunctor A).obj X)) := by
  rw [nativeDerivedCone, mapJoinCone_vertex, nativeDGCone_vertex]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
