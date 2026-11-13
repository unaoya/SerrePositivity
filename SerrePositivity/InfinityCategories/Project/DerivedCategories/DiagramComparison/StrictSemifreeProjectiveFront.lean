module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRawDAFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictFamilyEvaluationNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosedNerveFunctorNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SemifreeProjectivePointUnit

/-!
概要：同じ射影的native余錐の前面を、元の全strict評価に戻す。
方針：充満包含の後で同じnative前面の式と全評価の自然性を使う。
規約：全パラメーターと添字の全部の単体で比較する。
使われ方：3b-3 R6 U31、照合C1の同じ前面の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- C1の分割：同じ射影的前面を包含で戻すと、元の台の図式の全strict評価である。 -/
lemma strictSemifreeProjectiveFront_image :
    (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
      joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0]) ≫
    (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁ (strictSemifreeJoinShapeIso A).hom) ≫
      strictBarNativeProjectiveJoinFamily A SimplexCategoryᵒᵖ
        (strictSemifreePointUnderlyingFunctor A)
        (strictSemifreePointUnderlyingFunctor_projective A) ≫
      SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleProjectiveProperty A PUnit.{1})) =
    (nerveMap (strictSemifreePointUnderlyingFunctor A) ▷
      (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) ≫
      strictDiagramEvaluation SimplexCategoryᵒᵖ (ModuleCategory A PUnit.{1}) ≫
        closedNerveInclusion A (RightModule A PUnit.{1}) := by
  rw [← whiskerLeft_comp_assoc, strictSemifreeJoinShapeIso_inl,
    whiskerLeft_comp_assoc, strictBarNativeProjectiveJoinFamily_image]
  unfold strictBarNativeJoinFamilyAlong
  rw [whisker_exchange_assoc, strictBarNativeJoinFamily_front,
    strictModuleFamily_evaluation_factor]
  rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

/-- C1：同じ射影的native前面は元のstrict図式の全DG評価に一致する。 -/
lemma strictSemifreeProjectiveFront :
    let P := nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)
    let I := (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)
    (P ◁ joinInl I (Δ[0] : SSet.{u + 1})) ≫
      (P ◁ (strictSemifreeJoinShapeIso A).hom) ≫
        strictBarNativeProjectiveJoinFamily A SimplexCategoryᵒᵖ
          (strictSemifreePointUnderlyingFunctor A)
          (strictSemifreePointUnderlyingFunctor_projective A) =
    strictDiagramEvaluation SimplexCategoryᵒᵖ (ClosedCategory A (Semifree A)) ≫
      closedNerveInclusion A (Semifree A) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          ((semifreePointConstant A).comp (dgSemifreeToProjective A PUnit.{1})) := by
  dsimp only
  apply (cancel_mono
    (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
        (dgModuleProjectiveProperty A PUnit.{1})))).1
  simp only [Category.assoc]
  rw [strictSemifreeProjectiveFront_image]
  have hc : ((semifreePointConstant A).comp (dgSemifreeToProjective A PUnit.{1})).comp
      (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
        (dgModuleProjectiveProperty A PUnit.{1})) =
      (semifreePointConstant A).comp
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleSemifreeProperty A PUnit.{1})) := by
    refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
    intro X Y
    simp [EnrichedFunctor.comp_map, dgSemifreeToProjective, dgFullSubcategoryInclusion]
  rw [← SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    hc, closedNerveInclusion_dgFunctor]
  have hv : ((semifreePointConstant A).comp
      (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
        (dgModuleSemifreeProperty A PUnit.{1}))).onClosed =
      (semifreePointConstant A).onClosed ⋙
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleSemifreeProperty A PUnit.{1})).onClosed := by
    apply CategoryTheory.Functor.hext
    · intro X
      rfl
    · intro X Y f
      apply heq_of_eq
      have h := (EnrichedFunctor.forgetComp (semifreePointConstant A)
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleSemifreeProperty A PUnit.{1}))).hom.naturality f
      simp only [EnrichedFunctor.forgetComp_hom_app] at h
      change (((semifreePointConstant A).comp
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleSemifreeProperty A PUnit.{1}))).onClosed.map f) ≫ 𝟙 _ =
        𝟙 _ ≫ (((semifreePointConstant A).onClosed ⋙
          (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
            (dgModuleSemifreeProperty A PUnit.{1})).onClosed).map f) at h
      simpa only [Category.comp_id, Category.id_comp] using h
  have ht : strictSemifreePointUnderlyingFunctor A =
      (CategoryTheory.Functor.whiskeringRight SimplexCategoryᵒᵖ
        (ClosedCategory A (Semifree A)) (ModuleCategory A PUnit.{1})).obj
        (((semifreePointConstant A).comp
          (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
            (dgModuleSemifreeProperty A PUnit.{1}))).onClosed) := by
    rw [hv]
    rfl
  rw [ht, ← Category.assoc, strictDiagramEvaluation_postcompose, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
