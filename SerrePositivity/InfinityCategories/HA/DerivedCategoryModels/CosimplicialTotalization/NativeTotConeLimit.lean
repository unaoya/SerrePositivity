module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeRestriction
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.GammaReflectedBKComparisonEquality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralHomHolimComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentConeFamilyHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.UniverseHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComparisonEquivalence

/-!
概要：元のTot錐の同じ豊穣Hom族の同値性からnative極限性を得る。
方針：B06と二つの既存比較の同値性を合成し、指定族の極限判定を使う。
規約：IS-W2 B07・B08。元の錐と標準脚を取り換えない。模型圏の追加仮定なし。
使われ方：HA 1.2.4、複体の積Totのnative極限とD(A)輸送への入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable {A : Type u} [CommRing A]

/-- 指定されたTot錐全体の族を制限する同じ射が単体的ホモトピー同値。 -/
theorem nativeTotConeFamilyLift_equivalence
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence (nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x)) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram (liftedClosedDiagram X) x ⋙
      SSet.opFunctor).obj i) := fun i =>
    inferInstanceAs (KanComplex (SimplicialCategory.sHom x ((liftedClosedDiagram X).obj i)).op)
  have := bousfieldKanHolim_kanComplex
    (simplicialHomDiagram (liftedClosedDiagram X) x ⋙ SSet.opFunctor)
  rw [nativeTotConeFamilyLift_restriction]
  exact (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence.{u,u+1} (reflectedBKComparison_equivalence X x)).comp
      (reflectedHomHolimConeComparison_homotopyEquivalence (liftedClosedDiagram X) x)

/-- 元の積Totを頂点とする指定coherent錐は、全試験対象でnative極限錐。 -/
theorem nativeCoherentCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeCoherentCone X) := by
  exact coherentCone_isLimit_of_family_lifts (nativeCoherentCone X)
    (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
    (nativeCoherentCone_vertex X) (nativeTotConeFamilyLift X)
    (nativeTotConeFamilyLift_apex X) (nativeTotConeFamilyLift_equivalence X)

/-- 同じ全高次単体をdg nerveへ写した元のTot錐もnative極限錐。 -/
theorem nativeDGCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeDGCone X) := by
  exact (coherentComparison_isQCatEquivalence (R := A) (D := Complex A)).isLimitCone_iff
    (nativeCoherentCone X) |>.mp (nativeCoherentCone_isLimit X)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
