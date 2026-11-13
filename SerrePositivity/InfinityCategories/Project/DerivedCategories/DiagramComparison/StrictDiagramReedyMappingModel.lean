module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramLocalization
public import SerrePositivity.EInfinity.ProjectiveModel
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-!
概要：単体的・余単体的な非有界複体図式の、解像から作る全単体的Homの模型。
方針：既存のReedyモデルと余単体的解像を使い、弱同値を元の各成分の擬同型と照合する。
規約：モデル源はΔとΔᵒᵖだけ。∞局所化やcoherent変換空間との比較は別に証明する。
使われ方：HTT 4.2.4.4の加群版で用いる解像の写像空間。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

local instance : HasProducts.{u} (Complex A) := fun _ =>
  HomologicalComplex.instHasLimitsOfShape
local instance : HasProducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasLimitsOfShape

/-- Hovey §5.2のReedyモデルを元のΔ・Δᵒᵖ図式圏で使う。 -/
@[instance_reducible]
def strictDiagramReedyModelCategory : ModelCategory (StrictComplexDiagram A d) := by
  letI := EInfinity.projectiveModelCategory A
  cases d with
  | simplicial => exact Reedy.simplexOpModelCategory (Complex A)
  | cosimplicial => exact Reedy.simplexModelCategory (Complex A)

local instance : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

local instance : HasTerminal (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isTerminal.hasTerminal

/-- Reedyモデルの弱同値は、局所化で指定した同じobjectwise擬同型である。 -/
lemma strictDiagramReedyModelCategory_weakEquivalences :
    (strictDiagramReedyModelCategory A d).categoryWithWeakEquivalences.weakEquivalences =
      strictDiagramQuasiIsos A d := by
  cases d <;> rfl

/-- Hovey §5.2の既存の余単体的解像を、図式圏の中で取る。 -/
def strictDiagramSourceFrame (X : StrictComplexDiagram A d) :
    letI := strictDiagramReedyModelCategory A d
    Reedy.CofibrantResolution Reedy.simplex X := by
  letI := strictDiagramReedyModelCategory A d
  exact Reedy.cosimplicialResolution X

/-- 同じ図式の終対象への射を、既存モデル構造で分解する。 -/
def strictDiagramTargetFactorization (Y : StrictComplexDiagram A d) :
    letI := strictDiagramReedyModelCategory A d
    MorphismProperty.MapFactorizationData
      (trivialCofibrations (StrictComplexDiagram A d))
      (fibrations (StrictComplexDiagram A d)) (terminal.from Y) := by
  letI := strictDiagramReedyModelCategory A d
  exact MorphismProperty.factorizationData _ _ (terminal.from Y)

/-- 元の図式のfibrant置換の対象。元の各複体への追加の有界性は課さない。 -/
def strictDiagramFibrantTarget (Y : StrictComplexDiagram A d) : StrictComplexDiagram A d :=
  (strictDiagramTargetFactorization A d Y).Z

/-- 元の同じ図式から、指定したfibrant置換への比較。 -/
def strictDiagramFibrantTargetComparison (Y : StrictComplexDiagram A d) :
    Y ⟶ strictDiagramFibrantTarget A d Y :=
  (strictDiagramTargetFactorization A d Y).i

/-- 比較は各頂点で擬同型である。 -/
lemma strictDiagramFibrantTargetComparison_quasiIso (Y : StrictComplexDiagram A d) :
    strictDiagramQuasiIsos A d (strictDiagramFibrantTargetComparison A d Y) := by
  letI := strictDiagramReedyModelCategory A d
  rw [← strictDiagramReedyModelCategory_weakEquivalences]
  exact (strictDiagramTargetFactorization A d Y).hi.2

/-- 指定置換は実際にReedy fibrantである。 -/
lemma strictDiagramFibrantTarget_isFibrant (Y : StrictComplexDiagram A d) :
    letI := strictDiagramReedyModelCategory A d
    IsFibrant (strictDiagramFibrantTarget A d Y) := by
  letI := strictDiagramReedyModelCategory A d
  exact (isFibrant_iff_of_isTerminal
    (strictDiagramTargetFactorization A d Y).p terminalIsTerminal).mpr
      ⟨(strictDiagramTargetFactorization A d Y).hp⟩

/-- Hovey §5.4の解像Hom。n単体は元の図式圏の実際の自然変換である。 -/
def strictDiagramFrameMapping (X Y : StrictComplexDiagram A d) : SSet.{u} :=
  (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
    (strictDiagramSourceFrame A d X).obj).obj (strictDiagramFibrantTarget A d Y)

/-- 解像Homの全次数は、解像からfibrant置換への図式の自然変換そのもの。 -/
lemma strictDiagramFrameMapping_obj (X Y : StrictComplexDiagram A d)
    (n : SimplexCategoryᵒᵖ) :
    (strictDiagramFrameMapping A d X Y).obj n =
      ((strictDiagramSourceFrame A d X).obj.obj n.unop ⟶
        strictDiagramFibrantTarget A d Y) := rfl

/-- Hovey §5.4の既存horn充填を、同じ実解像Homに適用したKan性。 -/
lemma strictDiagramFrameMapping_kanComplex (X Y : StrictComplexDiagram A d) :
    SSet.KanComplex (strictDiagramFrameMapping A d X Y) := by
  letI := strictDiagramReedyModelCategory A d
  haveI := strictDiagramFibrantTarget_isFibrant A d Y
  exact HomotopyFunctionComplex.cosimplicialHom_kanComplex _
    (strictDiagramSourceFrame A d X).cofibrant
    (strictDiagramSourceFrame A d X).homotopicallyConstant
      (strictDiagramFibrantTarget A d Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
