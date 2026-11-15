module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationLiftedAdjunction
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanAdjunctionComparison

/-!
概要：Over上の元の評価frameと、持ち上げた要素圏の係数の同定。
方針：始点で評価する係数を保ち、元の評価frameのReedy条件を使う。
使われ方：HTT 4.2.4.4、RR02(a)の指定添字比較の弱同値性への入力。
規約：係数とframeを取り替えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance overFrames_complexModel : ModelCategory (Complex A) := EInfinity.projectiveModelCategory A
local instance overFrames_diagramModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance overFrames_hasInitial : HasInitial (Complex A) :=
  (isZero_zero (Complex A)).isInitial.hasInitial
local instance overFrames_frameInitial : HasInitial (SimplexCategory ⥤ Complex A) :=
  (isZero_zero (SimplexCategory ⥤ Complex A)).isInitial.hasInitial

/-- Overの対象の始点で、元のsource frameを評価する族。 -/
def strictDiagramFreeEvaluationOverFrames (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) : AsSmall.{u} (Over k) ⥤ SimplexCategory ⥤ Complex A :=
  AsSmall.down ⋙ Over.forget k ⋙ strictDiagramEvaluatedSourceFrames A d X

/-- 要素圏の指定射影とOverの始点での評価は、同じ係数を与える。 -/
def strictDiagramFreeEvaluationOverCoefficientsIso (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    strictDiagramFreeEvaluationLiftedToOver d k ⋙ strictDiagramFreeEvaluationOverFrames A d X k ≅
      Functor.Elements.π (strictDiagramFreeEvaluationLiftedWeight d k) ⋙
        strictDiagramFreeEvaluationBase A d X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro i j f; rfl)

lemma strictDiagramFreeEvaluationOverFrames_cofibrant (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) (t : AsSmall.{u} (Over k)) :
    Reedy.reedyLeft Reedy.simplex (cofibrations (Complex A))
      (initial.to ((strictDiagramFreeEvaluationOverFrames A d X k).obj t)) :=
  strictDiagramEvaluatedSourceFrame_cofibrant A d X ((AsSmall.down.obj t).left)

lemma strictDiagramFreeEvaluationOverFrames_homotopicallyConstant
    (X : StrictComplexDiagram A d) (k : strictDiagramIndex d) (t : AsSmall.{u} (Over k))
    {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences (Complex A) (((strictDiagramFreeEvaluationOverFrames A d X k).obj t).map f) :=
  strictDiagramEvaluatedSourceFrame_homotopicallyConstant A d X ((AsSmall.down.obj t).left) f

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
