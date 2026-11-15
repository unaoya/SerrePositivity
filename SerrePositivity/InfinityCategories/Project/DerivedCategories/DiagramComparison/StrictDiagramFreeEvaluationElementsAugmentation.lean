module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationOverComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationOverAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanAugmentationFrames

/-!
概要：Overへの指定比較と元の増大射の合成を、要素圏の元の余錐で表示する。
方針：添字変更の増大射の法則と、係数移送の法則を順に適用する。
使われ方：HTT 4.2.4.4、RR02(a)の元の自由増大射との一致の照合。
規約：Overの余錐を制限し、既存の係数同型の逆で移す。弱同値な別の射へ取り替えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance elementsAug_diagramModel : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance elementsAug_colimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩

/-- 同じOver余錐を制限し、元の要素圏の係数へ移した次数零余錐。 -/
def strictDiagramFreeEvaluationElementsCocone (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    Cocone (ConstantWeightHom.degree
      (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements
      (Functor.Elements.π (strictDiagramFreeEvaluationLiftedWeight d k) ⋙
        strictDiagramFreeEvaluationBase A d X) (SimplexCategory.mk 0)) :=
  (Cocone.precompose (ConstantWeightRealization.degreeMap _
    (strictDiagramFreeEvaluationOverCoefficientsIso A d X k).inv (SimplexCategory.mk 0))).obj
      ((strictDiagramFreeEvaluationOverCocone A d X k).whisker
        (strictDiagramFreeEvaluationLiftedToOver d k))

/-- 要素圏上の同じ指定余錐へのBK増大射。 -/
def strictDiagramFreeEvaluationElementsAugmentation (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :=
  FrameWeightRealization.bousfieldKanAugmentation
    (Functor.Elements.π (strictDiagramFreeEvaluationLiftedWeight d k) ⋙
      strictDiagramFreeEvaluationBase A d X) (strictDiagramFreeEvaluationElementsCocone A d X k)

/-- Over比較と増大の合成は、評価同型の後に要素圏の同じ増大を続けた射。 -/
lemma strictDiagramFreeEvaluationOverComparison_augmentation
    (X : StrictComplexDiagram A d) (k : strictDiagramIndex d) :
    strictDiagramFreeEvaluationOverComparison A d X k ≫
        strictDiagramFreeEvaluationOverAugmentation A d X k =
      (strictDiagramFreeEvaluationBousfieldKanIso A d X k).hom ≫
        strictDiagramFreeEvaluationElementsAugmentation A d X k := by
  unfold strictDiagramFreeEvaluationOverComparison strictDiagramFreeEvaluationOverAugmentation
  rw [Category.assoc, Category.assoc,
    FrameWeightRealization.bousfieldKanReindexMap_augmentation]
  congr 1
  change (FrameWeightRealization.map _
    (strictDiagramFreeEvaluationOverCoefficientsIso A d X k).inv).app _ ≫ _ = _
  exact FrameWeightRealization.bousfieldKanAugmentation_frame_naturality
    (strictDiagramFreeEvaluationOverCoefficientsIso A d X k).inv _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
