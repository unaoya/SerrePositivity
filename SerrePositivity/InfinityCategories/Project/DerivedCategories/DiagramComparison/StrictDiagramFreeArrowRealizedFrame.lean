module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowRealizationCofibrant
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanRealizationReedy
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanRealizationConstant

/-!
概要：指定自由arrow frameのBKパラメータ付き実現による余単体frameの条件。
方針：既存の自由frameの条件を、同じBK実現の検証済み持ち上げ法則へ渡す。
使われ方：HTT 4.2.4.4、RR02(a)の実際の余単体対象。
規約：指定増大射の弱同値性は別途証明する。
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


/-- 同じ自由arrow frameを、全標準単体のパラメータで実現した余単体対象。 -/
def strictDiagramFreeArrowRealizedFrame (X : StrictComplexDiagram A d) :
    SimplexCategory ⥤ StrictComplexDiagram A d :=
  SSet.stdSimplex ⋙ DiagramModel.FrameWeightRealization.bousfieldKanParameterRealization
    (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X)

/-- 既存の自由frameのcofibrancyを同じBK実現へ移す。 -/
lemma strictDiagramFreeArrowRealizedFrame_cofibrant (X : StrictComplexDiagram A d) :
    Reedy.reedyLeft Reedy.simplex (cofibrations (StrictComplexDiagram A d))
      (initial.to (strictDiagramFreeArrowRealizedFrame A d X)) := by
  apply DiagramModel.FrameWeightRealization.bousfieldKanRealization_reedy_cofibrant
    (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X)
  intro t
  exact strictDiagramFreeValueFrame_cofibrant A d X
    (AsSmall.down.obj t.unop.obj.1.unop) (AsSmall.down.obj t.unop.obj.2)

/-- 全構造射の弱同値性も、指定した自由frameから移す。 -/
lemma strictDiagramFreeArrowRealizedFrame_homotopicallyConstant
    (X : StrictComplexDiagram A d) {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences (StrictComplexDiagram A d)
      ((strictDiagramFreeArrowRealizedFrame A d X).map f) := by
  apply DiagramModel.FrameWeightRealization.bousfieldKanRealization_homotopicallyConstant
    (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X) _ _ f
  · intro t
    exact strictDiagramFreeValueFrame_cofibrant A d X
      (AsSmall.down.obj t.unop.obj.1.unop) (AsSmall.down.obj t.unop.obj.2)
  · intro t n m g
    exact strictDiagramFreeValueFrame_homotopicallyConstant A d X
      (AsSmall.down.obj t.unop.obj.1.unop) (AsSmall.down.obj t.unop.obj.2) g

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
