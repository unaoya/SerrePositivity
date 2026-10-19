module

public import SerrePositivity.KST.Spectra.CircleParameterTriangle
public import SerrePositivity.KST.Spectra.SpectrumZeroEvaluationTriangleOuter

/-!
概要：円の生成辺が与える、元の Sp 上の cotensor 評価の三角形の族。
方針：二対象の円柱の三角形を実際の普遍評価と合成する。
規約：二つの長辺を零三角形の同じ外辺へ厳密同定する。使われ方：loop 四角形の構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 円の生成辺に沿った、元の Sp 上の coherent な評価の三角形の族。 -/
def nativeCircleEvaluationTriangleFamily : Sp.{u} ⊗ (Δ[2] : SSet.{u + 1}) ⟶ Sp.{u} :=
  (𝟙 Sp.{u} ⊗ₘ circleParameterTriangle.{u, u + 1}) ≫
    nativeCotensorEvaluationFamily PointedSimplicialSet.circle

/-- 円の評価三角形の 1–2 辺は、元の基点評価の族。 -/
lemma nativeCircleEvaluationTriangleFamily_target :
    (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (0 : Fin 3)) ≫ nativeCircleEvaluationTriangleFamily =
      (𝟙 Sp.{u} ⊗ₘ EnrichedParameterCylinder.parameterEdge
        PointedSimplicialSet.circle.hom) ≫
          nativeCotensorEvaluationFamily PointedSimplicialSet.circle := by
  rw [nativeCircleEvaluationTriangleFamily, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp, circleParameterTriangle_target]

/-- 円の評価三角形の 0–2 辺も、同じ元の基点評価の族。 -/
lemma nativeCircleEvaluationTriangleFamily_source :
    (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫ nativeCircleEvaluationTriangleFamily =
      (𝟙 Sp.{u} ⊗ₘ EnrichedParameterCylinder.parameterEdge
        PointedSimplicialSet.circle.hom) ≫
          nativeCotensorEvaluationFamily PointedSimplicialSet.circle := by
  rw [nativeCircleEvaluationTriangleFamily, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp, circleParameterTriangle_source]

/-- 円の評価三角形の 0–1 辺は、native cotensor 関手の恒等辺の族。 -/
lemma nativeCircleEvaluationTriangleFamily_identity :
    (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (2 : Fin 3)) ≫ nativeCircleEvaluationTriangleFamily =
      fst Sp.{u} (Δ[1] : SSet.{u + 1}) ≫ nativeCotensor PointedSimplicialSet.circle := by
  rw [nativeCircleEvaluationTriangleFamily, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp, circleParameterTriangle_identity]
  change (fst Sp.{u} (Δ[1] : SSet.{u + 1}) ≫
    lift (𝟙 Sp.{u}) (SSet.const (EnrichedParameterCylinder.leftVertex
      PointedSimplicialSet.circle.right))) ≫ _ = _
  rw [Category.assoc, nativeCotensorEvaluationFamily_left]

/-- 円の評価三角形の 1–2 辺は、参照零三角形の外辺そのもの。 -/
lemma nativeCircleEvaluationTriangleFamily_target_zero :
    (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (0 : Fin 3)) ≫ nativeCircleEvaluationTriangleFamily =
      (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫
        nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle := by
  rw [nativeCircleEvaluationTriangleFamily_target, nativeZeroEvaluationTriangleFamily_outer]

/-- 円の評価三角形の 0–2 辺も、参照零三角形の同じ外辺。 -/
lemma nativeCircleEvaluationTriangleFamily_source_zero :
    (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫ nativeCircleEvaluationTriangleFamily =
      (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫
        nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle := by
  rw [nativeCircleEvaluationTriangleFamily_source, nativeZeroEvaluationTriangleFamily_outer]

end SerrePositivity.KST.Spectra.OmegaSpectrum
