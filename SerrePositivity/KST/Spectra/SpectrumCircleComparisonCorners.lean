module

public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonLeftEdges
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition

/-!
概要：元の比較 Hom 正方形の三つの隅を零頂点、残る隅を左右で共通に表示する。
方針：元の左辺と上辺および共通下辺の式を頂点で評価する。
規約：元の全 Hom の頂点を保持。使われ方：共通下辺の消去を元の正方形に適用する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の左側の二つの隅は、同じ元の零 Hom 頂点。 -/
lemma circleCompanionComparisonRawHomSquare_left_corner (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) (i : Fin 2) :
    (circleCompanionComparisonRawHomSquare z k).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 i) = (circleEvaluationPointedHom z).basepoint := by
  have h := circleCompanionComparisonRawHomSquare_left_vertex z k i
  change (circleCompanionComparisonRawHomSquare z k).app _
    ((SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _
      (stdSimplex.obj₀Equiv.symm i), stdSimplex.obj₀Equiv.symm i) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
  exact h

/-- 元の上側の二つの隅も、同じ元の零 Hom 頂点。 -/
lemma circleCompanionComparisonRawHomSquare_top_corner (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) (i : Fin 2) :
    (circleCompanionComparisonRawHomSquare z k).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner i 1) = (circleEvaluationPointedHom z).basepoint := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (circleEvaluationPointedHom z).right ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i))
      (circleCompanionComparisonRawHomSquare_includeSecond z k)
  change (circleCompanionComparisonRawHomSquare z k).app _
    (stdSimplex.obj₀Equiv.symm i,
      (SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app _
        (stdSimplex.obj₀Equiv.symm i)) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
  exact h

/-- 元の下側の隅は、左右の正方形で同じ元の頂点。 -/
lemma circleCompanionComparisonRawHomSquare_bottom_corner_common (z : Sp.{u} _⦋0⦌)
    (i : Fin 2) :
    (circleCompanionComparisonRawHomSquare z .left).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner i 0) =
    (circleCompanionComparisonRawHomSquare z .right).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner i 0) := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (circleEvaluationPointedHom z).right ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i))
      (circleCompanionComparisonRawHomSquare_skipSecond_common z)
  change (circleCompanionComparisonRawHomSquare z .left).app _
    (stdSimplex.obj₀Equiv.symm i,
      (SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _
        (stdSimplex.obj₀Equiv.symm i)) =
    (circleCompanionComparisonRawHomSquare z .right).app _
      (stdSimplex.obj₀Equiv.symm i,
        (SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _
          (stdSimplex.obj₀Equiv.symm i)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
  exact h

/-- 元の二つの正方形の共通下辺の終点。 -/
def circleCompanionComparisonMiddleVertex (z : Sp.{u} _⦋0⦌) :=
  (circleCompanionComparisonRawHomSquare z .left).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 0)

/-- 右下の隅は、左右とも元の同じ共通頂点。 -/
lemma circleCompanionComparisonRawHomSquare_middle_corner (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    (circleCompanionComparisonRawHomSquare z k).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 0) = circleCompanionComparisonMiddleVertex z := by
  cases k
  · rfl
  · exact (circleCompanionComparisonRawHomSquare_bottom_corner_common z 1).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum
