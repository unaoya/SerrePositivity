module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFrameArrowComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
概要：実際の二変数frame Homの値を、自由図式からのHomとして表示する。
方針：始点で評価したframeに終点での評価の左随伴を適用し、既存の随伴Hom同型を使う。
規約：元のframeを保持し、同型は任意の標的図式に自然。導来比較の弱同値性はまだ主張しない。
使われ方：HTT 4.2.4.4のRR02(a)、重みの実現へ渡す係数の表示。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : HasColimitsOfSize.{0, 0} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape
local instance : ModelCategory (Complex A) := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d

/-- 指定頂点での自由図式関手。Mathlibの評価の左随伴そのもの。 -/
def strictDiagramFreeAt (j : strictDiagramIndex d) : Complex A ⥤ StrictComplexDiagram A d :=
  evaluationLeftAdjoint (Complex A) j

/-- 元の評価との随伴。 -/
def strictDiagramFreeAtAdjunction (j : strictDiagramIndex d) :
    strictDiagramFreeAt A d j ⊣ (CategoryTheory.evaluation _ _).obj j :=
  evaluationAdjunctionRight (Complex A) j

/-- 評価の右Quillen性により、同じ自由図式関手は左Quillenである。 -/
lemma strictDiagramFreeAt_isLeftQuillen (j : strictDiagramIndex d) :
    Quillen.IsLeftQuillen (strictDiagramFreeAt A d j) := by
  have := (strictDiagramEvaluationAt_isQuillen A d j).2
  exact (Quillen.isLeftQuillen_iff_isRightQuillen
    (strictDiagramFreeAtAdjunction A d j)).mpr this

/-- 始点で評価した元のframeを、終点での自由図式へ送る。 -/
def strictDiagramFreeValueFrame (X : StrictComplexDiagram A d)
    (i j : strictDiagramIndex d) : SimplexCategory ⥤ StrictComplexDiagram A d :=
  strictDiagramEvaluatedSourceFrame A d X i ⋙ strictDiagramFreeAt A d j

/-- 自由図式のframe Homと元の値のHomとの、全標的に自然な同型。 -/
def strictDiagramFreeValueHomIso (X : StrictComplexDiagram A d)
    (i j : strictDiagramIndex d) :
    CosimplicialHom.cosimplicialHom (strictDiagramFreeValueFrame A d X i j) ≅
      (CategoryTheory.evaluation _ _).obj j ⋙
        CosimplicialHom.cosimplicialHom (strictDiagramEvaluatedSourceFrame A d X i) :=
  CosimplicialHom.adjunctionHomIsoSameUniverse (strictDiagramFreeAtAdjunction A d j) _

/-- 指定したHom要素圏の各値は、同じ自由frameからのHomと同型。 -/
def strictDiagramFreeArrowHomIso (X Y : StrictComplexDiagram A d)
    (t : StrictDiagramArrowElements.{u} d) :
    (CosimplicialHom.cosimplicialHom (strictDiagramFreeValueFrame A d X
      (AsSmall.down.obj t.obj.1.unop) (AsSmall.down.obj t.obj.2))).obj
        (strictDiagramFibrantTarget A d Y) ≅
      (strictDiagramFrameArrowDiagram A d X Y).obj t :=
  (strictDiagramFreeValueHomIso A d X _ _).app (strictDiagramFibrantTarget A d Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
