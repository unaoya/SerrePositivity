module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedColimits
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedMonomorphismCofibration
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LatchingPreservation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalMatching
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.DiagonalMatching

/-!
# 元の正規化標準単体の Reedy cofibrancy

概要：元の余単体的正規化複体は実射影モデルで Reedy cofibrant。
方針：同じ latching 余極限を保存し、標準境界の実 cofibration へ比較する。
規約：単体集合のモデル構造は入力せず、係数環の標数を制限しない。
使われ方：cofibrant 複体とのテンソルと元の frame Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Reedy
variable (A : Type u) [CommRing A]

set_option synthInstance.maxHeartbeats 40000 in
lemma normalizedSimplex_reedyCofibrant :
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    reedyLeft simplex (cofibrations (Complex A))
      (initial.to (SSet.stdSimplex ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ComplexLimits.normalizedFunctor_preservesSmallColimits A
  intro j
  have : Mono ((latchingComparison simplex j).app SSet.stdSimplex.{0}) := by
    induction j using SimplexCategory.rec with | _ n =>
    rw [← _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.standardBoundaryIso_fac n]
    infer_instance
  have h : cofibrations (Complex A)
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
        ((latchingComparison simplex j).app SSet.stdSimplex)) :=
    _root_.SerrePositivity.ComplexLimits.normalizedMonomorphism_cofibration A _
  have h' := ((cofibrations (Complex A)).arrow_iso_iff
    (latchingComparison_preservedIso simplex (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A)
      SSet.stdSimplex j)).mpr h
  exact ((cofibrations (Complex A)).arrow_iso_iff
    (latchingInitialArrowIso simplex j (SSet.stdSimplex ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A))).mp h'

end SerrePositivity.ComplexLimits
