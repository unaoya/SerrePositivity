module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeFamilyBoundaries
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteNativeTotCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality

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
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ離散入力への制限を全パラメータの関手単体集合で読む。 -/
def rawDiscreteTotFunctorDiagram :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶
      (ihom (nerve (CosimplicialObject (ModuleCat.{u} A)))).obj (derivedInfinityCategory A) :=
  curry ((β_ _ _).hom ≫
    (𝟙 _ ⊗ₘ nerveMap (discreteDiagramFunctor A)) ≫ derivedTotEvaluationFamily A)

/-- 同じ離散入力の全raw錐を、関手単体集合の一つの錐にする。 -/
def rawDiscreteTotFunctorCone : JoinCone (rawDiscreteTotFunctorDiagram A) := by
  refine ⟨curry ((β_ _ _).hom ≫
    (𝟙 _ ⊗ₘ nerveMap (discreteDiagramFunctor A)) ≫ derivedTotConeFamily A), ?_⟩
  rw [← curry_natural_left]
  apply congrArg curry
  have he :
      (nerve (CosimplicialObject (ModuleCat.{u} A)) ◁
        joinInr (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) ≫ (β_ _ _).hom ≫
        (𝟙 _ ⊗ₘ nerveMap (discreteDiagramFunctor A)) =
      (β_ _ _).hom ≫ (𝟙 _ ⊗ₘ nerveMap (discreteDiagramFunctor A)) ≫
        (joinInr (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
            𝟙 (nerve (CosimplicialObject (Complex A)))) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  have h := congrArg (· ≫ derivedTotConeFamily A) he
  simp only [Category.assoc] at h
  rw [derivedTotConeFamily_right] at h
  exact h

/-- 同じraw関手圏錐を固定Mで評価すると、同じ元の全指定離散錐に戻る。 -/
theorem rawDiscreteTotFunctorCone_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    (rawDiscreteTotFunctorCone A).val ≫ evaluateFunctorAt (ComposableArrows.mk₀ M) =
      (rawCosimplicialModuleCone A M).val := by
  rw [rawDiscreteTotFunctorCone, strictFamilyCurry_evaluateAt]
  have he :
      lift (SSet.const (ComposableArrows.mk₀ M)) (𝟙 _) ≫ (β_ _ _).hom ≫
        (𝟙 _ ⊗ₘ nerveMap (discreteDiagramFunctor A)) =
      lift (𝟙 (join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))))
          (SSet.const (ComposableArrows.mk₀ ((discreteDiagramFunctor A).obj M))) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    apply Prod.ext
    · rfl
    · change (Functor.const (Fin (n.unop.len + 1))).obj M ⋙ discreteDiagramFunctor A =
        (Functor.const (Fin (n.unop.len + 1))).obj ((discreteDiagramFunctor A).obj M)
      apply CategoryTheory.Functor.hext
      · intro i
        rfl
      · intro i j f
        exact heq_of_eq ((discreteDiagramFunctor A).map_id M)
  have h := congrArg (· ≫ derivedTotConeFamily A) he
  simp only [Category.assoc] at h
  rw [derivedTotConeFamily_at_lift] at h
  rw [rawCosimplicialModuleCone, joinConeOfDiagramEq_val]
  exact h

/-- 同じraw全離散錐は、全パラメータ関手圏でも極限錐。 -/
theorem rawDiscreteTotFunctorCone_isLimit : IsLimitCone (rawDiscreteTotFunctorCone A) := by
  apply isLimitCone_of_pointwise
  intro M
  obtain ⟨M, rfl⟩ := ComposableArrows.mk₀_surjective M
  exact (isLimitCone_iff_of_cone_val_eq _ _ (rawDiscreteTotFunctorCone_at A M)).2
    (rawCosimplicialModuleCone_isLimit A M)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
