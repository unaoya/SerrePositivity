module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductReplacementCoefficient
public import SerrePositivity.InfinityCategories.F2.Ind.StrictLeftSectionWeightedEvaluation

/-!
概要：全単体の相対切断の replacement を、元の strict 図式の replacement と weighted nerve へ写す。
方針：底の単体圏の射列で始点の元の切断を評価し、元の添字の射列を保持する。
規約：全単体・全添字の同じ評価射として面・退化を同時に保つ。
使われ方：共同 weighted 分類と全切断の実現を結ぶ大域 scaffold。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B)

/-- 同じ全切断の replacement を、元の全空間の replacement へ写す大域評価。 -/
def sectionProductReplacementMap :
    simplicialReplacement (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) ⟶
      simplicialReplacement (leftFibrationTotalDiagram F) where
  app _ := ↾fun s ↦ ⟨s.1 ⋙ CategoryTheory.Prod.fst I (TransportSimplexCategory B),
    sectionProductReplacementCoefficient F s⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    exact sectionProductReplacementCoefficient_naturality F α.unop s

/-- 元の添字の射列は、元の積の第一射影で得た同じ射列。 -/
lemma sectionProductReplacementMap_index :
    sectionProductReplacementMap F ≫ simplicialReplacementProjection (leftFibrationTotalDiagram F) =
      simplicialReplacementProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) ≫
        nerveMap (CategoryTheory.Prod.fst I (TransportSimplexCategory B)) := rfl

/-- 元の同じ全切断を元の共同 weighted nerve へ評価する大域射。 -/
def sectionProductWeightedEvaluation :
    simplicialReplacement (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) ⟶
      weightedNerve (leftFibrationTotalDiagram F) :=
  sectionProductReplacementMap F ≫ tautScaffold (leftFibrationTotalDiagram F)

/-- 同じ大域射は、元の添字への射影を厳密に保持する。 -/
lemma sectionProductWeightedEvaluation_index :
    sectionProductWeightedEvaluation F ≫ weightedNerveProjection (leftFibrationTotalDiagram F) =
      simplicialReplacementProjection (strictLeftTransportSectionDiagram F ⋙ kanObjectForget) ≫
        nerveMap (CategoryTheory.Prod.fst I (TransportSimplexCategory B)) := by
  rw [sectionProductWeightedEvaluation, Category.assoc, tautScaffold_projection,
    sectionProductReplacementMap_index]

end SerrePositivity.InfinityCategories.F2.Ind
