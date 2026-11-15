module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanAugmentation

/-!
概要：指定自由arrow frameのBK実現から、元のsource frameの次数零への実増大射。
方針：既存の全frameの増大を次数零で評価し、元の実現随伴で転置する。
規約：元のframeと増大射を保持する。弱同値性は別の証明対象。
使われ方：HTT 4.2.4.4のRR02(a)、実際のframe Hom比較の源。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape
local instance : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
variable (X : StrictComplexDiagram A d)

/-- 元の全frameの増大射を次数零で評価した指定余錐。 -/
def strictDiagramFreeArrowZeroCocone :
    Cocone (ConstantWeightHom.degree (StrictDiagramArrowElements.{u} d)ᵒᵖ
      (strictDiagramFreeArrowFrame A d X) (SimplexCategory.mk 0)) where
  pt := (strictDiagramSourceFrame A d X).obj.obj (SimplexCategory.mk 0)
  ι := Functor.whiskerRight (strictDiagramFreeArrowAugmentation A d X)
    ((CategoryTheory.evaluation SimplexCategory (StrictComplexDiagram A d)).obj
      (SimplexCategory.mk 0))

/-- 自由arrow frameの元のBK重みによる実現。 -/
def strictDiagramFreeArrowRealization : StrictComplexDiagram A d :=
  (FrameWeightRealization.functor (StrictDiagramArrowElements.{u} d)ᵒᵖ
    (strictDiagramFreeArrowFrame A d X)).obj
      (bousfieldKanWeight ((StrictDiagramArrowElements.{u} d)ᵒᵖ)ᵒᵖ)

/-- 指定したsource frameの次数零への、同じ実現随伴からの増大射。 -/
def strictDiagramFreeArrowRealizationAugmentation :
    strictDiagramFreeArrowRealization A d X ⟶
      (strictDiagramSourceFrame A d X).obj.obj (SimplexCategory.mk 0) :=
  FrameWeightRealization.bousfieldKanAugmentation
    (strictDiagramFreeArrowFrame A d X) (strictDiagramFreeArrowZeroCocone A d X)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
