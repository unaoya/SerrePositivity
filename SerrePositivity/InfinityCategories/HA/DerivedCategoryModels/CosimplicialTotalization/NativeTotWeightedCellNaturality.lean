module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedReindex
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
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ全セル族は、初点を保つ全面・退化に可換。 -/
theorem nativeTotWeightedCellFamily_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFamily A ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      (nerve (CosimplicialObject (Complex A)) ◁
        joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.stdSimplex.map α)) ≫
          nativeTotWeightedCellFamily A σ := by
  unfold nativeTotWeightedCellFamily
  rw [nativeTotWeightedCellFunctor_reindex, strictSimplexFunctorEvaluation_pullback,
    ← Category.assoc, ← whiskerLeft_comp, ← Category.assoc, ← whiskerLeft_comp]
  congr 2
  exact (joinStdSimplexIso_point_naturality α).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
