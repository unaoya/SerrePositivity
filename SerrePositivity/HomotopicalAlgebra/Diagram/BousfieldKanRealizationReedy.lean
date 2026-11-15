module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanParameterizedRealization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBoundary
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.FiniteTensorAdjunction

/-!
概要：BKパラメータ付き実現の標準単体はReedy cofibrant。
方針：有限tensorと左随伴の値の既存の同型で境界を移し、latchingの同型を使う。
使われ方：HTT 4.2.4.4、RR02(a)の実際のframeの境界条件。
SSetのモデル構造を仮定せず、Cのcofibrationだけで述べる。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))

include hA in
/-- 実際のBK実現における有限境界tensorの包含。 -/
lemma bousfieldKanRealization_boundary_cofibration (n : ℕ) :
    cofibrations C (SubcomplexTensor.inclusion (SSet.boundary.{w} n)
      (StandardCosimplicial.diagram (bousfieldKanParameterRealization K A))) := by
  let F := bousfieldKanParameterRealization K A
  have h := (cofibrations C).comp_mem _ _
    ((cofibrations C).of_isIso
      (InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso F
        (SSet.boundary.{w} n).toSSet).hom)
    (bousfieldKanParameterRealization_map_cofibration K A hA (SSet.boundary.{w} n).ι)
  exact (InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso_inclusion F
    (SSet.boundary.{w} n)) ▸ h

include hA in
/-- 標準単体に沿うBK実現は、元のCのモデル構造でReedy cofibrant。 -/
lemma bousfieldKanRealization_reedy_cofibrant :
    reedyLeft simplex (cofibrations C)
      (initial.to (StandardCosimplicial.diagram (bousfieldKanParameterRealization K A))) := by
  intro j
  induction j using SimplexCategory.rec with | _ n =>
  exact ((cofibrations C).arrow_iso_iff
    (latchingInitialArrowIso simplex (SimplexCategory.mk n)
      (StandardCosimplicial.diagram (bousfieldKanParameterRealization K A)))).mp
    (((cofibrations C).arrow_iso_iff
      (boundaryTensorArrowIso
        (StandardCosimplicial.diagram (bousfieldKanParameterRealization K A)) n)).mp
      (bousfieldKanRealization_boundary_cofibration K A hA n))

end SerrePositivity.DiagramModel.FrameWeightRealization
