module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotTailCellEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotFunctorCosliceFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexStrictNerveComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellIdentification
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexEvaluationAtParameter

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の全join族の右境界は、元の全閉零評価のnerveと一致する。 -/
theorem nativeTotJoinFamily_right :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInr (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) ≫
      nativeTotJoinFamily A = nativeTotClosedEvaluationNerve A ≫
        closedNerveInclusion A (Complex A) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨d, ⟨σ⟩⟩
  have hc := congrArg (fun f =>
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInr (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1})) ≫ f)
      (nativeTotJoinFamily_cell A σ)
  rw [← whiskerLeft_comp_assoc, joinInr_joinMap,
    nativeTotWeightedCellFamily_tail] at hc
  have hv := congrArg
    (fun f : nerve (CosimplicialObject (Complex A)) ⊗ (Δ[n] : SSet.{u+1}) ⟶
      dgNerve A (Complex A) => f.app (Opposite.op ⦋n⦌) (d, ULift.up (𝟙 ⦋n⦌))) hc
  exact hv.trans (nativeTotTailCellEvaluation_diagonal A σ d)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
