module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluationFrames

/-!
概要：評価source frameの増大射を、元の全添字に自然な族として固定する。
方針：指定された図式圏の増大射の各成分を用いる。
規約：頂点ごとの独立な置換を選ばず、元の添字射の自然性を保持する。
使われ方：HTT 4.2.4.4のRR02、共通frameによる値の比較の入力。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance evaluatedAugmentationModel : ModelCategory (Complex A) :=
  EInfinity.projectiveModelCategory A
local instance evaluatedAugmentationDiagramModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 元の指定増大射を全添字で評価した、自然な余単体的増大射の族。 -/
def strictDiagramEvaluatedAugmentation (X : StrictComplexDiagram A d) :
    strictDiagramEvaluatedSourceFrames A d X ⟶ X ⋙ Functor.const SimplexCategory where
  app j :=
    { app n := ((strictDiagramSourceFrame A d X).augmentation.app n).app j
      naturality := by
        intro n m f
        exact congrArg (fun a => a.app j)
          ((strictDiagramSourceFrame A d X).augmentation.naturality f) }
  naturality := by
    intro i j f
    apply NatTrans.ext
    funext n
    exact ((strictDiagramSourceFrame A d X).augmentation.app n).naturality f

/-- 全ての添字と余単体次数で、同じ増大射は擬同型である。 -/
lemma strictDiagramEvaluatedAugmentation_weak (X : StrictComplexDiagram A d)
    (j : strictDiagramIndex d) (n : SimplexCategory) :
    weakEquivalences (Complex A)
      (((strictDiagramEvaluatedAugmentation A d X).app j).app n) := by
  have h := (strictDiagramSourceFrame A d X).augmentation_weakEquivalence n
  cases d <;> exact h j

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
