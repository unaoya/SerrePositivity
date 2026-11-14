module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationOverFrames
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationBousfieldKan

/-!
概要：持ち上げた要素圏の実BK実現から、Overの実BK実現への指定比較は弱同値。
方針：元の係数同型の逆と指定右随伴の比較を合成し、それぞれの弱同値性を使う。
使われ方：HTT 4.2.4.4、RR02(a)の自由実現の評価値の比較。
規約：元の評価点・元の係数・指定比較射を保つ。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance overComparison_complexModel : ModelCategory (Complex A) := EInfinity.projectiveModelCategory A
local instance overComparison_diagramModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance overComparison_colimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance overComparison_initial : HasInitial (Complex A) :=
  (isZero_zero (Complex A)).isInitial.hasInitial
local instance overComparison_frameInitial : HasInitial (SimplexCategory ⥤ Complex A) :=
  (isZero_zero (SimplexCategory ⥤ Complex A)).isInitial.hasInitial

/-- 元の自由実現の評価同型の後、係数の同定と指定Over比較を続ける。 -/
def strictDiagramFreeEvaluationOverComparison (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    (strictDiagramFreeArrowRealization A d X).obj k ⟶
      (FrameWeightRealization.functor (AsSmall.{u} (Over k))
        (strictDiagramFreeEvaluationOverFrames A d X k)).obj
        (bousfieldKanWeight (AsSmall.{u} (Over k))ᵒᵖ) :=
  (strictDiagramFreeEvaluationBousfieldKanIso A d X k).hom ≫
    (((FrameWeightRealization.family
      (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements).mapIso
        (strictDiagramFreeEvaluationOverCoefficientsIso A d X k)).inv.app _) ≫
    FrameWeightRealization.bousfieldKanReindexMap
      (strictDiagramFreeEvaluationLiftedToOver d k) (strictDiagramFreeEvaluationOverFrames A d X k)

/-- 評価同型と元の右随伴の比較を合成した、指定実比較の弱同値性。 -/
lemma strictDiagramFreeEvaluationOverComparison_weakEquivalence
    (X : StrictComplexDiagram A d) (k : strictDiagramIndex d) :
    weakEquivalences (Complex A) (strictDiagramFreeEvaluationOverComparison A d X k) := by
  unfold strictDiagramFreeEvaluationOverComparison
  apply (weakEquivalences (Complex A)).comp_mem
  · exact (weakEquivalences (Complex A)).of_isIso _
  · apply (weakEquivalences (Complex A)).comp_mem
    · change weakEquivalences (Complex A)
        ((((FrameWeightRealization.family
          (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements).mapIso
            (strictDiagramFreeEvaluationOverCoefficientsIso A d X k)).app _).inv)
      exact (weakEquivalences (Complex A)).of_isIso _
    · exact FrameWeightRealization.bousfieldKanReindexMap_weakEquivalence_of_adjunction
        (strictDiagramFreeEvaluationLiftedAdjunction d k)
        (strictDiagramFreeEvaluationOverFrames A d X k)
        (strictDiagramFreeEvaluationOverFrames_cofibrant A d X k)
        (fun t _ _ f => strictDiagramFreeEvaluationOverFrames_homotopicallyConstant A d X k t f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
