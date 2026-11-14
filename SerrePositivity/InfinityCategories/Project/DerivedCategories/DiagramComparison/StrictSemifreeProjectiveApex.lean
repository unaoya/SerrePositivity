module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeNormalizedProjectiveModule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictClosedVertexEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRawDAFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.ClosedNerveFunctorNaturality

/-!
概要：元のnative全余錐族の射影的apexを、同じ正規化barの全関手と照合する。
方針：充満包含後で既存の全apexの式と閉零セルの全評価を使う。
規約：全射列・全HA成分の等式であり、apexを選び直さない。
使われ方：3b-3 R6 U39、照合C2。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet CartesianMonoidalCategory MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- C2：同じ射影的native全余錐族のapexは元の正規化barの全関手。 -/
lemma strictSemifreeProjectiveApex :
    let P := nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)
    let I := (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)
    lift (𝟙 P) (SSet.stdSimplex.isTerminalObj₀.from P) ≫
      (P ◁ joinInr I (Δ[0] : SSet.{u + 1})) ≫
        (P ◁ (strictSemifreeJoinShapeIso A).hom) ≫
          strictBarNativeProjectiveJoinFamily A SimplexCategoryᵒᵖ
            (strictSemifreePointUnderlyingFunctor A)
            (strictSemifreePointUnderlyingFunctor_projective A) =
      nerveMap (strictSemifreeNormalizedProjectiveModule A) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveDGModules A PUnit.{1}) := by
  dsimp only
  apply (cancel_mono
    (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
        (dgModuleProjectiveProperty A PUnit.{1})))).1
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, strictSemifreeJoinShapeIso_inr,
    strictBarNativeProjectiveJoinFamily_image]
  unfold strictBarNativeJoinFamilyAlong
  rw [whisker_exchange_assoc, strictBarNativeJoinFamily_apex]
  have ht : lift (𝟙 (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)))
      (SSet.stdSimplex.isTerminalObj₀.from _) ≫
        (nerveMap (strictSemifreePointUnderlyingFunctor A) ▷ (Δ[0] : SSet.{u + 1})) =
      nerveMap (strictSemifreePointUnderlyingFunctor A) ≫
        lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _) := by
    rw [lift_whiskerRight, comp_lift, Category.comp_id, Category.id_comp]
    congr 1
  rw [← Category.assoc, ht, Category.assoc, strictBarApexCellEvaluation]
  have hn : strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
      (strictBarNormalizedFunctor A SimplexCategoryᵒᵖ ⋙ strictBarClosedVertexFunctor A) =
      (nerveMap (strictBarNormalizedFunctor A SimplexCategoryᵒᵖ) ▷ Δ[0]) ≫
        strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
          (strictBarClosedVertexFunctor A) := by
    unfold strictSimplexFunctorEvaluation
    rfl
  rw [hn, ← Category.assoc]
  rw [closedNerveInclusion_dgFunctor]
  have h := congrArg nerveMap (strictSemifreeNormalizedProjectiveModule_underlying A)
  change nerveMap (strictSemifreeNormalizedProjectiveModule A) ≫
    nerveMap (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleProjectiveProperty A PUnit.{1})).onClosed =
      nerveMap (strictSemifreePointUnderlyingFunctor A) ≫
        nerveMap (strictBarNormalizedFunctor A SimplexCategoryᵒᵖ) at h
  rw [← Category.assoc _ (nerveMap (dgFullSubcategoryInclusion A
    (RightModule A PUnit.{1}) (dgModuleProjectiveProperty A PUnit.{1})).onClosed) _, h]
  simp only [Category.assoc]
  congr 1
  have hc := strictClosedVertexEvaluation A (𝟭 (ModuleCategory A PUnit.{1}))
  change lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _) ≫
    strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
      (strictBarClosedVertexFunctor A) = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (RightModule A PUnit.{1}) at hc
  rw [lift_whiskerRight_assoc, ← hc, comp_lift_assoc, Category.comp_id]
  congr 1

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
