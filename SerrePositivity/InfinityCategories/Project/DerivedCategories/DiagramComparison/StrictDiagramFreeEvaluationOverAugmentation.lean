module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationOverFrames
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanColimitAugmentation
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：Over上の元の評価frameのBK実現から、評価点の次数零への増大射。
方針：恒等射の終対象性を宇宙移送し、指定終対象余錐の増大射を使う。
使われ方：HTT 4.2.4.4、RR02(a)の実評価での増大射の弱同値性。
規約：終対象への構造射と元の評価frameを保持する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance overAug_complexModel : ModelCategory (Complex A) := EInfinity.projectiveModelCategory A
local instance overAug_diagramModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance overAug_colimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance overAug_initial : HasInitial (Complex A) :=
  (isZero_zero (Complex A)).isInitial.hasInitial
local instance overAug_frameInitial : HasInitial (SimplexCategory ⥤ Complex A) :=
  (isZero_zero (SimplexCategory ⥤ Complex A)).isInitial.hasInitial

/-- 同じ宇宙へ移した恒等射は、Overの終対象。 -/
def strictDiagramFreeEvaluationOverTerminal (k : strictDiagramIndex d) :
    IsTerminal (AsSmall.up.obj (Over.mk (𝟙 k)) : AsSmall.{u} (Over k)) :=
  IsTerminal.ofUniqueHom
    (fun t => AsSmall.up.map (Over.mkIdTerminal.from (AsSmall.down.obj t)))
    (fun t f => by
      apply ULift.ext
      exact Over.mkIdTerminal.hom_ext _ _)

/-- 終対象への元の構造射を使う、次数零の余錐。 -/
def strictDiagramFreeEvaluationOverCocone (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    Cocone (ConstantWeightHom.degree (AsSmall.{u} (Over k))
      (strictDiagramFreeEvaluationOverFrames A d X k) (SimplexCategory.mk 0)) :=
  coconeOfDiagramTerminal (strictDiagramFreeEvaluationOverTerminal d k) _

/-- 同じOver実現から元の評価frameの次数零へ向かう指定増大射。 -/
def strictDiagramFreeEvaluationOverAugmentation (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    (FrameWeightRealization.functor (AsSmall.{u} (Over k))
      (strictDiagramFreeEvaluationOverFrames A d X k)).obj
      (bousfieldKanWeight (AsSmall.{u} (Over k))ᵒᵖ) ⟶
        (strictDiagramEvaluatedSourceFrame A d X k).obj (SimplexCategory.mk 0) :=
  FrameWeightRealization.bousfieldKanAugmentation
    (strictDiagramFreeEvaluationOverFrames A d X k) (strictDiagramFreeEvaluationOverCocone A d X k)

lemma strictDiagramFreeEvaluationOverAugmentation_weakEquivalence
    (X : StrictComplexDiagram A d) (k : strictDiagramIndex d) :
    weakEquivalences (Complex A) (strictDiagramFreeEvaluationOverAugmentation A d X k) :=
  FrameWeightRealization.bousfieldKanAugmentation_weakEquivalence_of_terminal
    (strictDiagramFreeEvaluationOverFrames A d X k) (strictDiagramFreeEvaluationOverCocone A d X k)
    (strictDiagramFreeEvaluationOverFrames_cofibrant A d X k)
    (fun t _ _ f => strictDiagramFreeEvaluationOverFrames_homotopicallyConstant A d X k t f)
    (strictDiagramFreeEvaluationOverTerminal d k) (colimitOfDiagramTerminal _ _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
