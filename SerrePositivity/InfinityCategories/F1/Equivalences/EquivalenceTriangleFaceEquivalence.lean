module

public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceTriangleInitialIso
public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceTriangleFaceEvaluation
public import SerrePositivity.InfinityCategories.Core.EquivalencePathFinalLifting

/-!
概要：元の可逆三角形の三つの面への射影は同値。
方針：初頂点評価の逆を定値三角形で与え、可逆 path の端点評価で各面を比較する。
規約：元の同じ面の制限そのものの同値性。
使われ方：元の比較三角形の Hom から比較 span への射影。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 可逆三角形の初頂点評価は、定値三角形を逆とする同値。 -/
lemma equivalenceTriangleEvaluation_zero_isQCatEquivalence
    (Y : SSet.{u}) [Quasicategory Y] :
    IsQCatEquivalence (equivalenceTriangleEvaluation Y 0) := by
  refine ⟨equivalenceTriangleConstant Y, ⟨equivalenceTriangleInitialIso Y⟩, ⟨?_⟩⟩
  rw [equivalenceTriangleConstant_evaluation]

/-- 同じ可逆三角形の最初の面への制限は同値。 -/
lemma equivalenceTriangleFace_two_isQCatEquivalence
    (Y : SSet.{u}) [Quasicategory Y] : IsQCatEquivalence (equivalenceTriangleFace Y 2) := by
  have h : IsQCatEquivalence (equivalenceTriangleFace Y 2 ≫ equivalencePathEndpoint Y 0) := by
    rw [equivalenceTriangleFace_endpoint]
    exact equivalenceTriangleEvaluation_zero_isQCatEquivalence Y
  exact (isQCatEquivalence_of_trivialKanFibration (equivalencePathEndpoint Y 0)).cancel_right h

/-- 同じ可逆三角形の中間頂点評価は同値。 -/
lemma equivalenceTriangleEvaluation_one_isQCatEquivalence
    (Y : SSet.{u}) [Quasicategory Y] :
    IsQCatEquivalence (equivalenceTriangleEvaluation Y 1) := by
  have h := (equivalenceTriangleFace_two_isQCatEquivalence Y).comp
    (isQCatEquivalence_of_trivialKanFibration (equivalencePathEndpoint Y 1))
  have hi : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  simpa only [equivalenceTriangleFace_endpoint, hi] using h

/-- 同じ可逆三角形の各面への制限は同値。 -/
lemma equivalenceTriangleFace_isQCatEquivalence
    (Y : SSet.{u}) [Quasicategory Y] (i : Fin 3) :
    IsQCatEquivalence (equivalenceTriangleFace Y i) := by
  apply (isQCatEquivalence_of_trivialKanFibration (equivalencePathEndpoint Y 0)).cancel_right
  rw [equivalenceTriangleFace_endpoint]
  fin_cases i
  · exact equivalenceTriangleEvaluation_one_isQCatEquivalence Y
  · exact equivalenceTriangleEvaluation_zero_isQCatEquivalence Y
  · exact equivalenceTriangleEvaluation_zero_isQCatEquivalence Y

end SerrePositivity.InfinityCategories
