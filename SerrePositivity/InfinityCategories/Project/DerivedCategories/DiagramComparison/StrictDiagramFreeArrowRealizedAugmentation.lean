module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowRealizedFrame
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanFrameAugmentationZero

/-!
概要：指定自由arrow frameのBK実現から元のsource frameへの実増大射。
方針：同じ自由frame余錐に全次数の転置を適用し、次数零の一致を移す。
使われ方：HTT 4.2.4.4、RR02(a)の元のframe Hom比較への接続。
規約：弱同値性は別の証明対象として残す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape
local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d



/-- 同じ自由arrowの余錐から、元のsource frameへの全次数の実増大射。 -/
def strictDiagramFreeArrowRealizedAugmentation (X : StrictComplexDiagram A d) :
    strictDiagramFreeArrowRealizedFrame A d X ⟶ (strictDiagramSourceFrame A d X).obj :=
  DiagramModel.FrameWeightRealization.bousfieldKanFrameAugmentation
    (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X)
    (strictDiagramSourceFrame A d X).obj (strictDiagramFreeArrowAugmentation A d X)

/-- 全frame実現の次数零を、元の指定BK実現と比較する同型。 -/
def strictDiagramFreeArrowRealizedZeroIso (X : StrictComplexDiagram A d) :
    (strictDiagramFreeArrowRealizedFrame A d X).obj (SimplexCategory.mk 0) ≅
      strictDiagramFreeArrowRealization A d X :=
  (DiagramModel.FrameWeightRealization.functor (StrictDiagramArrowElements.{u} d)ᵒᵖ
    (strictDiagramFreeArrowFrame A d X)).mapIso
      (DiagramModel.FrameWeightRealization.bousfieldKanZeroParameterIso
        (StrictDiagramArrowElements.{u} d)ᵒᵖ)

/-- 次数零の射は、元の実現増大射を同じ単位同型で移したものに等しい。 -/
lemma strictDiagramFreeArrowRealizedAugmentation_zero (X : StrictComplexDiagram A d) :
    (strictDiagramFreeArrowRealizedZeroIso A d X).hom ≫
        strictDiagramFreeArrowRealizationAugmentation A d X =
      (strictDiagramFreeArrowRealizedAugmentation A d X).app (SimplexCategory.mk 0) :=
  DiagramModel.FrameWeightRealization.bousfieldKanFrameAugmentation_zero
    (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X)
    (strictDiagramSourceFrame A d X).obj (strictDiagramFreeArrowAugmentation A d X)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
