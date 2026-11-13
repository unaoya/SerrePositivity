module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramReedyMappingModel

/-!
概要：同じReedy複体図式の関手的分解と、両変数で自然な実解像Homを作る。
方針：複体の生成モデルの関手的分解を、既存のReedy関手的分解へ渡す。
規約：Δ・Δᵒᵖに固定し、∞局所化との比較を仮定しない。
使われ方：HTT 4.2.4.4の加群版で用いる全変換空間の解像。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

local instance : HasProducts.{u} (Complex A) := fun _ =>
  HomologicalComplex.instHasLimitsOfShape
local instance : HasProducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasLimitsOfShape

/-- Hovey §5.2のReedy構成に、元の複体の第一関手的分解を入力する。 -/
lemma strictDiagramReedy_cof_hasFunctorialFactorization :
    letI := strictDiagramReedyModelCategory A d
    (cofibrations (StrictComplexDiagram A d)).HasFunctorialFactorization
      (trivialFibrations (StrictComplexDiagram A d)) := by
  letI := EInfinity.projectiveModelCategory A
  haveI := EInfinity.projectiveModelCategory_cofibrantlyGenerated A
  haveI := hasFunctorialFactorization_cofibration_trivialFibration
    (EInfinity.projectiveGeneratingCofibrations A)
    (EInfinity.projectiveGeneratingTrivialCofibrations A)
  cases d with
  | simplicial =>
    change (Reedy.reedyLeft Reedy.simplexOp (cofibrations (Complex A))).HasFunctorialFactorization
      (Reedy.reedyRight Reedy.simplexOp (fibrations (Complex A)) ⊓
        (weakEquivalences (Complex A)).functorCategory SimplexCategoryᵒᵖ)
    rw [← Reedy.reedyRight_trivialFibrations_eq]
    exact Reedy.FunctorFactorizationSequence.hasFunctorialFactorization Reedy.simplexOp
      (fun _ _ h => Opposite.unop_injective (SimplexCategory.ext h))
      (fun n => ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)
  | cosimplicial =>
    change (Reedy.reedyLeft Reedy.simplex (cofibrations (Complex A))).HasFunctorialFactorization
      (Reedy.reedyRight Reedy.simplex (fibrations (Complex A)) ⊓
        (weakEquivalences (Complex A)).functorCategory SimplexCategory)
    rw [← Reedy.reedyRight_trivialFibrations_eq]
    exact Reedy.FunctorFactorizationSequence.hasFunctorialFactorization Reedy.simplex
      (fun _ _ h => SimplexCategory.ext h) (fun n => ⟨SimplexCategory.mk n, rfl⟩)

/-- Hovey §5.2のReedy構成に、元の複体の第二関手的分解を入力する。 -/
lemma strictDiagramReedy_fib_hasFunctorialFactorization :
    letI := strictDiagramReedyModelCategory A d
    (trivialCofibrations (StrictComplexDiagram A d)).HasFunctorialFactorization
      (fibrations (StrictComplexDiagram A d)) := by
  letI := EInfinity.projectiveModelCategory A
  haveI := EInfinity.projectiveModelCategory_cofibrantlyGenerated A
  haveI := hasFunctorialFactorization_trivialCofibration_fibration
    (EInfinity.projectiveGeneratingCofibrations A)
    (EInfinity.projectiveGeneratingTrivialCofibrations A)
  cases d with
  | simplicial =>
    change (Reedy.reedyLeft Reedy.simplexOp (cofibrations (Complex A)) ⊓
      (weakEquivalences (Complex A)).functorCategory SimplexCategoryᵒᵖ).HasFunctorialFactorization
        (Reedy.reedyRight Reedy.simplexOp (fibrations (Complex A)))
    rw [← Reedy.reedyLeft_trivialCofibrations_eq]
    exact Reedy.FunctorFactorizationSequence.hasFunctorialFactorization Reedy.simplexOp
      (fun _ _ h => Opposite.unop_injective (SimplexCategory.ext h))
      (fun n => ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)
  | cosimplicial =>
    change (Reedy.reedyLeft Reedy.simplex (cofibrations (Complex A)) ⊓
      (weakEquivalences (Complex A)).functorCategory SimplexCategory).HasFunctorialFactorization
        (Reedy.reedyRight Reedy.simplex (fibrations (Complex A)))
    rw [← Reedy.reedyLeft_trivialCofibrations_eq]
    exact Reedy.FunctorFactorizationSequence.hasFunctorialFactorization Reedy.simplex
      (fun _ _ h => SimplexCategory.ext h) (fun n => ⟨SimplexCategory.mk n, rfl⟩)

local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance : HasTerminal (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isTerminal.hasTerminal

/-- 元の図式圏の第一関手的分解の実データ。 -/
def strictDiagramCofFactorizationData :
    (cofibrations (StrictComplexDiagram A d)).FunctorialFactorizationData
      (trivialFibrations (StrictComplexDiagram A d)) := by
  haveI := strictDiagramReedy_cof_hasFunctorialFactorization A d
  exact MorphismProperty.functorialFactorizationData _ _

/-- 元の図式圏の第二関手的分解の実データ。 -/
def strictDiagramFibFactorizationData :
    (trivialCofibrations (StrictComplexDiagram A d)).FunctorialFactorizationData
      (fibrations (StrictComplexDiagram A d)) := by
  haveI := strictDiagramReedy_fib_hasFunctorialFactorization A d
  exact MorphismProperty.functorialFactorizationData _ _

/-- Hovey §5.4の関手的解像から作る、両変数で自然な実際の全単体的Hom。 -/
def strictDiagramResolutionMapping :
    (StrictComplexDiagram A d)ᵒᵖ ⥤ StrictComplexDiagram A d ⥤ SSet.{u} :=
  HomotopyFunctionComplex.chosenResolutionHom
    (strictDiagramCofFactorizationData A d) (strictDiagramFibFactorizationData A d)

/-- 同じ両変数の解像HomはKan複体である。 -/
lemma strictDiagramResolutionMapping_kanComplex
    (X : (StrictComplexDiagram A d)ᵒᵖ) (Y : StrictComplexDiagram A d) :
    SSet.KanComplex (((strictDiagramResolutionMapping A d).obj X).obj Y) :=
  HomotopyFunctionComplex.chosenResolutionHom_kanComplex
    (strictDiagramCofFactorizationData A d) (strictDiagramFibFactorizationData A d) X Y

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
