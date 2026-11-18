module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeValueFrame

/-!
概要：実係数を表示する自由frameのReedy cofibrancyと構造射の弱同値性。
方針：既存の左Quillen関手によるframeの保存則を、同じ評価frameへ適用する。
規約：自由frameの全添字族のprojective cofibrancyは主張しない。
使われ方：HTT 4.2.4.4のRR02(a)、重みの実現の値ごとのframe条件。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ModelCategory (Complex A) := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance : HasInitial (Complex A) := (isZero_zero (Complex A)).isInitial.hasInitial
local instance : HasInitial (SimplexCategory ⥤ Complex A) :=
  (isZero_zero (SimplexCategory ⥤ Complex A)).isInitial.hasInitial
local instance : HasInitial (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial
local instance : HasInitial (SimplexCategory ⥤ StrictComplexDiagram A d) :=
  (isZero_zero (SimplexCategory ⥤ StrictComplexDiagram A d)).isInitial.hasInitial

/-- 同じ自由frameは、図式圏のReedyモデルで余単体的にcofibrant。 -/
lemma strictDiagramFreeValueFrame_cofibrant (X : StrictComplexDiagram A d)
    (i j : strictDiagramIndex d) :
    Reedy.reedyLeft Reedy.simplex (cofibrations (StrictComplexDiagram A d))
      (initial.to (strictDiagramFreeValueFrame A d X i j)) := by
  have := (strictDiagramFreeAtAdjunction A d j).isLeftAdjoint
  have := strictDiagramFreeAt_isLeftQuillen A d j
  exact leftQuillen_frame_reedyCofibrant (strictDiagramFreeAt A d j)
    (strictDiagramEvaluatedSourceFrame A d X i)
    (strictDiagramEvaluatedSourceFrame_cofibrant A d X i)

/-- 同じ自由frameの全構造射は、元の図式圏で弱同値。 -/
lemma strictDiagramFreeValueFrame_homotopicallyConstant (X : StrictComplexDiagram A d)
    (i j : strictDiagramIndex d) {m n : SimplexCategory} (f : m ⟶ n) :
    weakEquivalences (StrictComplexDiagram A d)
      ((strictDiagramFreeValueFrame A d X i j).map f) := by
  have := strictDiagramFreeAt_isLeftQuillen A d j
  exact leftQuillen_frame_homotopicallyConstant (strictDiagramFreeAt A d j)
    (strictDiagramEvaluatedSourceFrame A d X i)
    (strictDiagramEvaluatedSourceFrame_cofibrant A d X i)
    (fun a => strictDiagramEvaluatedSourceFrame_homotopicallyConstant A d X i a) f

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
