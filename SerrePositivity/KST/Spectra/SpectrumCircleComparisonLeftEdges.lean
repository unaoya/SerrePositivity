module

public import SerrePositivity.KST.Spectra.SpectrumCircleNativeComparisonTriangles
public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonTopConstant

/-!
概要：元の比較 Hom 正方形の参照側の左辺と両方の上辺を、元の零 Hom に厳密同定する。
方針：元の参照三角形の定値性と、共通下辺の始点・元の companion loop の端点を使う。
規約：元の基点を保持。使われ方：正方形の境界の合成から中央経路を消去する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleComparisonLeftEdgesSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の全 Hom に表示した二つの正方形も、同じ元の中央経路を下辺に持つ。 -/
lemma circleCompanionComparisonRawHomSquare_skipSecond_common (z : Sp.{u} _⦋0⦌) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      circleCompanionComparisonRawHomSquare z .left =
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      circleCompanionComparisonRawHomSquare z .right := by
  simp only [circleCompanionComparisonRawHomSquare, ← Category.assoc,
    circleCompanionComparisonHomSquare_skipSecond]

/-- 元の参照側の正方形の左辺は、元の参照三角形から得る定値経路。 -/
lemma circleCompanionComparisonRawHomSquare_skipFirst_right_constant (z : Sp.{u} _⦋0⦌) :
    ∃ v, lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      circleCompanionComparisonRawHomSquare z .right = SSet.const v := by
  have h0 := (CoherentPathCoordinates.triangleTrace_constant_congr
    (circleZeroFunctorTriangleAt z)).mpr
      (CotensorCompatible.zeroEvaluationTriangleTrace_constant PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z))
  obtain ⟨v, hv⟩ := (CoherentPathCoordinates.triangleTrace_constant_congr
    (circleNativeComparisonTriangle_right z)).mpr h0
  rw [circleCompanionComparisonRawHomSquare, ← Category.assoc,
    circleCompanionComparisonHomSquare_skipFirst]
  simp only [hv, SSet.const_comp]
  exact ⟨_, rfl⟩

/-- 元の二つの正方形の始点の隅は、元の共通下辺の同じ始点。 -/
lemma circleCompanionComparisonRawHomSquare_corner_common (z : Sp.{u} _⦋0⦌) :
    (circleCompanionComparisonRawHomSquare z .left).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    (circleCompanionComparisonRawHomSquare z .right).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (circleEvaluationPointedHom z).right ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (circleCompanionComparisonRawHomSquare_skipSecond_common z)
  change (circleCompanionComparisonRawHomSquare z .left).app _
    (stdSimplex.obj₀Equiv.symm 0, (SSet.const (X := (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _ (stdSimplex.obj₀Equiv.symm 0)) =
    (circleCompanionComparisonRawHomSquare z .right).app _
      (stdSimplex.obj₀Equiv.symm 0, (SSet.const (X := (Δ[1] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _ (stdSimplex.obj₀Equiv.symm 0)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
  exact h

/-- 元の参照側の左辺は、同じ元の零 Hom に厳密に定値。 -/
lemma circleCompanionComparisonRawHomSquare_skipFirst_right (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      circleCompanionComparisonRawHomSquare z .right =
      SSet.const (circleEvaluationPointedHom z).basepoint := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_of_vertex
    (circleCompanionComparisonRawHomSquare_skipFirst_right_constant z)
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (circleEvaluationPointedHom z).right ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (circleCompanionComparisonRawHomSquare_skipFirst_left z)
  change (circleCompanionComparisonRawHomSquare z .left).app _
    ((SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _
      (stdSimplex.obj₀Equiv.symm 0), stdSimplex.obj₀Equiv.symm 0) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
  have hv := circleEvaluationCompanion_vertex z (0 : Fin 2)
  change _ = (circleEvaluationPointedHom z).basepoint at hv
  have hh := h.trans hv
  change (circleCompanionComparisonRawHomSquare z .right).app _
    ((SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _
      (stdSimplex.obj₀Equiv.symm 0), stdSimplex.obj₀Equiv.symm 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex]
  exact (circleCompanionComparisonRawHomSquare_corner_common z).symm.trans hh

/-- 元の左右の左辺の両端は、同じ元の零 Hom 頂点。 -/
lemma circleCompanionComparisonRawHomSquare_left_vertex (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) (i : Fin 2) :
    (lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      circleCompanionComparisonRawHomSquare z k).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm i) = (circleEvaluationPointedHom z).basepoint := by
  cases k
  · rw [circleCompanionComparisonRawHomSquare_skipFirst_left]
    exact circleEvaluationCompanion_vertex z i
  · rw [circleCompanionComparisonRawHomSquare_skipFirst_right, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex]

/-- 元の比較正方形の上辺も、同じ元の零 Hom に厳密に定値。 -/
lemma circleCompanionComparisonRawHomSquare_includeSecond (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      circleCompanionComparisonRawHomSquare z k =
      SSet.const (circleEvaluationPointedHom z).basepoint := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_of_vertex
    (circleCompanionComparisonRawHomSquare_includeSecond_constant z k)
  have h := circleCompanionComparisonRawHomSquare_left_vertex z k (1 : Fin 2)
  change (circleCompanionComparisonRawHomSquare z k).app _
    ((SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app _
      (stdSimplex.obj₀Equiv.symm 1), stdSimplex.obj₀Equiv.symm 1) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
  change (circleCompanionComparisonRawHomSquare z k).app _
    (stdSimplex.obj₀Equiv.symm 0, (SSet.const (X := (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app _ (stdSimplex.obj₀Equiv.symm 0)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex]
  exact h

end SerrePositivity.KST.Spectra.OmegaSpectrum
