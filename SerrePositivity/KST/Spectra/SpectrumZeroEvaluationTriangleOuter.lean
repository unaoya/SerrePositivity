module

public import SerrePositivity.KST.Spectra.EnrichedTransformationTriangleOuter
public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderEdge
public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderEvaluation
public import SerrePositivity.KST.Spectra.SpectrumNativeZeroEvaluationTriangle
public import SerrePositivity.KST.Spectra.SpectrumNativeCotensorEvaluation

/-!
概要：零評価の三角形の外辺と、元の基点評価の族の厳密な一致。
方針：標準単体の制限を順序付き円柱の選び直しへ送り、評価の制限と比較する。
規約：全対象・全高次単体での等式。使われ方：円の生成辺とのホーンの貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance zeroTriangleOuterSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
namespace CotensorCompatible

/-- 共通解像上の零三角形の外辺は、元の評価の基点の辺への制限そのもの。 -/
lemma zeroEvaluationTriangleFamily_outer (A : PointedSimplicialSet.{u}) :
    (𝟙 (SimplicialNerve (Object A)) ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫
        zeroEvaluationTriangleFamily A =
      (𝟙 (SimplicialNerve (Object A)) ⊗ₘ
        EnrichedParameterCylinder.parameterEdge.{u, u + 1} A.hom) ≫ evaluationNerveFamily A := by
  have hn := EnrichedOrderedCylinder.nerveSimplexFamily_naturality
    (C := Object A) (SimplexCategory.δ (1 : Fin 3))
  change (𝟙 (SimplicialNerve (Object A)) ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫
      EnrichedOrderedCylinder.nerveSimplexFamily 2 = _ at hn
  rw [zeroEvaluationTriangleFamily, ← Category.assoc, hn,
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, zeroEvaluationTriangleEnriched,
    EnrichedTransformationTriangle.functor_outer]
  rw [evaluationNerveFamily, ← Category.assoc,
    EnrichedParameterCylinder.nervePair_parameterEdge,
    Category.assoc, evaluationCylinderInfinityMap, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
    evaluationCylinderEnriched]
  rw [EnrichedOrderedCylinder.bridge_evaluation A.hom]
  rfl

end CotensorCompatible

/-- 元の Sp 上でも、零三角形の外辺は基点評価の族と厳密に一致する。 -/
lemma nativeZeroEvaluationTriangleFamily_outer (A : PointedSimplicialSet.{u}) :
    (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫ nativeZeroEvaluationTriangleFamily A =
      (𝟙 Sp.{u} ⊗ₘ EnrichedParameterCylinder.parameterEdge.{u, u + 1} A.hom) ≫
        nativeCotensorEvaluationFamily A := by
  have commute {K L : SSet.{u + 1}} (f : K ⟶ L) :
      (𝟙 Sp.{u} ⊗ₘ f) ≫ ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 L) =
        ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 K) ≫
          (𝟙 (SimplicialNerve (CotensorCompatible.Object A)) ⊗ₘ f) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [nativeZeroEvaluationTriangleFamily, ← Category.assoc, commute, Category.assoc,
    CotensorCompatible.zeroEvaluationTriangleFamily_outer,
    nativeCotensorEvaluationFamily]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ CotensorCompatible.evaluationNerveFamily A)
    (commute (EnrichedParameterCylinder.parameterEdge.{u, u + 1} A.hom)).symm


end SerrePositivity.KST.Spectra.OmegaSpectrum
