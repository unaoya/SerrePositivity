module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotJoinRightBoundary
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeFamily
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotFamilyBoundaries

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
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- D02右境界：元の全評価関手の同じ導来像へ戻る。 -/
theorem derivedTotConeFamily_right :
    (joinInr (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
        derivedTotEvaluationFamily A := by
  have he :
      (joinInr (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
        𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ (β_ _ _).hom ≫
        (nerve (CosimplicialObject (Complex A)) ◁
          joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.inv) =
      (β_ _ _).hom ≫ (nerve (CosimplicialObject (Complex A)) ◁ nativeTotIndexIso.inv) ≫
        (nerve (CosimplicialObject (Complex A)) ◁
          joinInr (Δ[0] : SSet.{u+1})
            ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) := by
    rw [← Category.assoc, BraidedCategory.braiding_naturality,
      Category.assoc, id_tensorHom, ← whiskerLeft_comp, joinInr_joinMap,
      whiskerLeft_comp]
  have h := congrArg (fun k => k ≫ nativeTotJoinFamily A ≫
    complexSemifreeResolutionInfinity A) he
  simp only [Category.assoc] at h
  have ht := congrArg (fun k =>
      (β_ _ _).hom ≫ (nerve (CosimplicialObject (Complex A)) ◁ nativeTotIndexIso.inv) ≫
        k ≫ complexSemifreeResolutionInfinity A) (nativeTotJoinFamily_right A)
  simp only [Category.assoc] at ht
  have hev : (β_ _ _).hom ≫
      (nerve (CosimplicialObject (Complex A)) ◁ nativeTotIndexIso.inv) ≫
        nativeTotClosedEvaluationNerve A =
      strictCosimplicialEvaluationNerve A ≫ nerveMap (complexToClosed A) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  have hev' := congrArg (fun k => k ≫ closedNerveInclusion A (Complex A) ≫
    complexSemifreeResolutionInfinity A) hev
  simp only [Category.assoc] at hev'
  exact (h.trans ht).trans hev'

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
