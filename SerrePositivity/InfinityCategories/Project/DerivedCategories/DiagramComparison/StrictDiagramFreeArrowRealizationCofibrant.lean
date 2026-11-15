module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeValueFrameConditions
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanFrameCofibrancy

/-!
概要：元の自由arrow frameの指定BK実現はcofibrant。
方針：既存の自由frameのReedy cofibrancyを、BK重みの直接持ち上げに渡す。
規約：SSetのモデル存在入力や、重みのcofibrancyの仮定を加えない。
使われ方：HTT 4.2.4.4のRR02(a)、元の実増大射の源の模型条件。
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

/-- 同じ自由arrow frameの実現は、元の複体図式のReedyモデルでcofibrant。 -/
lemma strictDiagramFreeArrowRealization_isCofibrant (X : StrictComplexDiagram A d) :
    IsCofibrant (strictDiagramFreeArrowRealization A d X) := by
  apply DiagramModel.FrameWeightRealization.bousfieldKanRealization_isCofibrant
    (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X)
  intro t
  exact strictDiagramFreeValueFrame_cofibrant A d X
    (AsSmall.down.obj t.unop.obj.1.unop) (AsSmall.down.obj t.unop.obj.2)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
