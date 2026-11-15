module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationIndex
public import SerrePositivity.HomotopicalAlgebra.Diagram.ElementsCopowerFrames
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightPostcomposition

/-!
概要：指定自由arrow frameを評価すると、同じ始点の係数の余積frameになる。
方針：各次数の余積添字をULiftし、添字の射は余積の挿入で照合する。
使われ方：HTT 4.2.4.4、RR02(a)の実現の要素圏表示への適用。
規約：元の自由frameと元の評価点を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance freeEvaluationFrames_hasColimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance freeEvaluationFrames_hasCoproducts : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape
local instance freeEvaluationFrames_modelCategory : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 各arrowの始点での、元のsource frameの値の族。 -/
def strictDiagramFreeEvaluationBase (X : StrictComplexDiagram A d) :
    (StrictDiagramArrowElements.{u} d)ᵒᵖ ⥤ SimplexCategory ⥤ Complex A :=
  strictDiagramFreeArrowIndex d ⋙ CategoryTheory.Prod.snd _ _ ⋙
    strictDiagramEvaluatedSourceFrames A d X

/-- 小さいHom添字を、実現のHom宇宙へ標準的に持ち上げる。 -/
def strictDiagramFreeEvaluationLiftedWeight (k : strictDiagramIndex d) :
    (StrictDiagramArrowElements.{u} d)ᵒᵖ ⥤ Type u :=
  strictDiagramFreeEvaluationWeight d k ⋙ CategoryTheory.uliftFunctor.{u, 0}

/-- 元の小さい添字とULiftした添字の余積を、up・downで同定する。 -/
def strictDiagramFreeEvaluationCopowerIso (I : Type) (V : Complex A) :
    (∐ fun _ : I => V) ≅ ∐ fun _ : ULift.{u} I => V where
  hom := Sigma.map' ULift.up (fun _ => 𝟙 V)
  inv := Sigma.map' ULift.down (fun _ => 𝟙 V)
  hom_inv_id := by apply Sigma.hom_ext; intro x; simp
  inv_hom_id := by apply Sigma.hom_ext; intro x; cases x; simp

/-- 評価した自由frameと、同じ係数・同じHom添字による余積frameとの同型。 -/
def strictDiagramFreeEvaluationFramesIso (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :
    FrameWeightRealization.postFrames (StrictDiagramArrowElements.{u} d)ᵒᵖ
      (strictDiagramFreeArrowFrame A d X)
      ((CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj k) ≅
    ElementsCopower.frames (strictDiagramFreeEvaluationLiftedWeight d k)
      (strictDiagramFreeEvaluationBase A d X) :=
  NatIso.ofComponents (fun t => NatIso.ofComponents (fun n =>
    strictDiagramFreeEvaluationCopowerIso A _
      (((strictDiagramFreeEvaluationBase A d X).obj t).obj n)) (by
    intro n m f
    apply Sigma.hom_ext
    intro h
    simp [strictDiagramFreeEvaluationCopowerIso, FrameWeightRealization.postFrames, strictDiagramFreeArrowFrame,
      strictDiagramFreeValueFrameFamily, strictDiagramFreeAtFunctor,
      strictDiagramFreeAt, strictDiagramFreeEvaluationBase,
      strictDiagramFreeEvaluationLiftedWeight, strictDiagramFreeEvaluationWeight, ElementsCopower.frames, ElementsCopower.diagram,
      Category.assoc] <;> rfl)) (by
    intro t s f
    apply NatTrans.ext
    funext n
    apply Sigma.hom_ext
    intro h
    simp [strictDiagramFreeEvaluationCopowerIso, FrameWeightRealization.postFrames, strictDiagramFreeArrowFrame,
      strictDiagramFreeValueFrameFamily, strictDiagramFreeAtFunctor,
      strictDiagramFreeAtReindex, strictDiagramFreeAt, strictDiagramFreeEvaluationBase,
      strictDiagramFreeEvaluationLiftedWeight, strictDiagramFreeEvaluationWeight, ElementsCopower.frames, ElementsCopower.diagram,
      Category.assoc] <;> rfl)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
