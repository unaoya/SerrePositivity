module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDGCone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConeSourceApex

/-!
概要：元のTot錐全体上の全豊穣Homの指定族と、その頂点評価を与える。
方針：既存の標準coslice切断の前合成の族を、同じnative錐へ特殊化する。
規約：IS-W2 B04・B05。錐、頂点、全パラメータを保持する。
使われ方：HA 1.2.4、G10の元のnative錐の極限性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable {A : Type u} [CommRing A]

/-- 同じnative Tot錐全体上に、元の反転Homの全パラメータを持ち上げる族。 -/
def nativeTotConeFamilyLift (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj (SimplicialCategory.sHom x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))).op ⟶
        coherentConeSectionSpace (nativeCoherentCone X).val (coherentNerveVertex x) :=
  coherentConeSourceFamily (nativeCoherentCone X)
    (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
    (nativeCoherentCone_vertex X) x

/-- 元の族を頂点で評価すると、同じ標準coslice fiber比較を返す。 -/
theorem nativeTotConeFamilyLift_apex (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    nativeTotConeFamilyLift X x ≫ coherentConeApexEvaluation (nativeCoherentCone X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeCoherentCone_vertex X) x =
    coherentCosliceFiberComparison x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)) :=
  coherentConeSourceFamily_evaluation (nativeCoherentCone X)
    (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
    (nativeCoherentCone_vertex X) x

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
