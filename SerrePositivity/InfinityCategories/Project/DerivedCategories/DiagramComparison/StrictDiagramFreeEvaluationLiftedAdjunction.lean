module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationCofinality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationFrames
public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsUniverseLift

/-!
概要：実現に使うULift済み要素圏から、同じ宇宙のOver圏への指定随伴。
方針：既存の要素圏の上下の同値と、既存のOverへの随伴を合成する。
使われ方：HTT 4.2.4.4、RR02(a)の実評価での指定添字比較。
規約：元のarrowと評価点を変えず、要素の宇宙だけを移す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DiagramModel
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (d : StrictDiagramDirection) (k : strictDiagramIndex d)

/-- 元の要素へdownし、指定した合成関手でOverへ送る。 -/
def strictDiagramFreeEvaluationLiftedToOver :
    (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements ⥤ AsSmall.{u} (Over k) :=
  ElementsUniverseLift.down (strictDiagramFreeEvaluationWeight d k) ⋙
    strictDiagramFreeEvaluationSmallToOver d k

/-- 指定した左随伴の後に、要素のupを合成する。 -/
def strictDiagramFreeEvaluationLiftedSection :
    AsSmall.{u} (Over k) ⥤ (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements :=
  (AsSmall.down ⋙ strictDiagramFreeEvaluationSection d k) ⋙
    ElementsUniverseLift.up (strictDiagramFreeEvaluationWeight d k)

/-- 実現に使う要素圏とOverとの、元の随伴の合成。 -/
def strictDiagramFreeEvaluationLiftedAdjunction :
    strictDiagramFreeEvaluationLiftedSection.{u} d k ⊣
      strictDiagramFreeEvaluationLiftedToOver d k :=
  (strictDiagramFreeEvaluationSmallAdjunction d k).comp
    (ElementsUniverseLift.equivalence (strictDiagramFreeEvaluationWeight d k)).toAdjunction

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
