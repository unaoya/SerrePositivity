module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationCoconeLegs

/-!
概要：元の自由arrow実現の増大射は、各評価値で、従って元のReedyモデルで弱同値。
方針：実係数の余錐の脚を同定し、表示同型の増大射保存を合成してOverの弱同値へ戻す。
使われ方：HTT 4.2.4.4、RR02(a)の指定自由frameの元の増大射。
規約：別の弱同値な射でなく、strictDiagramFreeArrowRealizationAugmentationそのもの。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance freeAugWeak_complexModel : ModelCategory (Complex A) := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
local instance freeAugWeak_diagramModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance freeAugWeak_colimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance freeAugWeak_coproducts : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape
local instance freeAugWeak_products : ∀ (i j : strictDiagramIndex d),
    HasProductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasLimitsOfShape

lemma strictDiagramFreeEvaluationElementsAugmentation_eq (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    strictDiagramFreeEvaluationElementsAugmentation A d X k =
      FrameWeightRealization.bousfieldKanAugmentation
        (Functor.Elements.π (strictDiagramFreeEvaluationLiftedWeight d k) ⋙
          strictDiagramFreeEvaluationBase A d X)
        (ElementsCopower.elementsZeroCocone (strictDiagramFreeEvaluationLiftedWeight d k)
          (strictDiagramFreeEvaluationBase A d X) (strictDiagramFreeEvaluationCopowerCocone A d X k)) := by
  change ((FrameWeightRealization.adjunction _ _).homEquiv _ _).symm _ =
    ((FrameWeightRealization.adjunction _ _).homEquiv _ _).symm _
  apply congrArg ((FrameWeightRealization.adjunction _ _).homEquiv _ _).symm
  apply congrArg (fun t => FrameWeightRealization.bousfieldKanZeroWeight _ ≫ t)
  apply congrArg (ConstantWeightHom.homEquiv _ _ (SimplexCategory.mk 0) _).symm
  apply NatTrans.ext
  funext e
  rw [strictDiagramFreeEvaluationElementsCocone_leg, strictDiagramFreeEvaluationCopowerCocone_leg]

/-- 指定比較とOverの増大射の合成は、元の自由増大射の評価値そのもの。 -/
lemma strictDiagramFreeEvaluationOverComparison_augmentation_eq
    (X : StrictComplexDiagram A d) (k : strictDiagramIndex d) :
    strictDiagramFreeEvaluationOverComparison A d X k ≫
        strictDiagramFreeEvaluationOverAugmentation A d X k =
      (strictDiagramFreeArrowRealizationAugmentation A d X).app k := by
  rw [strictDiagramFreeEvaluationOverComparison_augmentation,
    strictDiagramFreeEvaluationElementsAugmentation_eq]
  dsimp only [strictDiagramFreeEvaluationBousfieldKanIso,
    strictDiagramFreeEvaluationRealizationIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  simp only [Category.assoc]
  rw [ElementsCopower.realizationIso_hom_augmentation]
  exact (congrArg (fun f =>
    ((FrameWeightRealization.postIso (StrictDiagramArrowElements.{u} d)ᵒᵖ
      (evaluationAdjunctionLeft (Complex A) k)
      (strictDiagramFreeArrowFrame A d X)).app _).hom ≫ f)
    (FrameWeightRealization.augmentation_frameIso
      (strictDiagramFreeEvaluationFramesIso A d X k)
      (strictDiagramFreeEvaluationPostCocone A d X k))).trans
    (FrameWeightRealization.postIso_augmentation (StrictDiagramArrowElements.{u} d)ᵒᵖ
      (evaluationAdjunctionLeft (Complex A) k) (strictDiagramFreeArrowFrame A d X)
      (strictDiagramFreeArrowZeroCocone A d X))

lemma strictDiagramFreeArrowRealizationAugmentation_app_weak
    (X : StrictComplexDiagram A d) (k : strictDiagramIndex d) :
    weakEquivalences (Complex A) ((strictDiagramFreeArrowRealizationAugmentation A d X).app k) := by
  rw [← strictDiagramFreeEvaluationOverComparison_augmentation_eq]
  exact (weakEquivalences (Complex A)).comp_mem _ _
    (strictDiagramFreeEvaluationOverComparison_weakEquivalence A d X k)
    (strictDiagramFreeEvaluationOverAugmentation_weakEquivalence A d X k)

/-- 同じ元の自由増大射は、図式圏のReedyモデルでも弱同値。 -/
lemma strictDiagramFreeArrowRealizationAugmentation_weak (X : StrictComplexDiagram A d) :
    weakEquivalences (StrictComplexDiagram A d) (strictDiagramFreeArrowRealizationAugmentation A d X) := by
  have h := strictDiagramFreeArrowRealizationAugmentation_app_weak A d X
  cases d <;> exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
