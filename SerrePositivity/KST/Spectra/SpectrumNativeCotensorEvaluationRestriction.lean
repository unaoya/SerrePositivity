module

public import SerrePositivity.KST.Spectra.SpectrumNativeCotensorEvaluation
public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationRestriction
public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderNerveRestriction

/-!
概要：Sp の二変数の cotensor 評価の族と、円柱のパラメータ制限の両立。
方針：nerve の pairing の制限式と元の評価円柱の制限式を合成する。
規約：共通解像上でも元の Sp 上でも全単体の射の等式。
使われ方：円の基点上の零評価から、零角を持つ loop 四角形へ移す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeEvaluationRestrictionSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
namespace CotensorCompatible

/-- 共通解像上の二変数の評価は、元の制限された円柱の図式へ厳密に制限される。 -/
lemma evaluationNerveFamily_restriction (A : PointedSimplicialSet.{u})
    {K : SSet.{u}} (i : K ⟶ A.right) :
    (𝟙 (SimplicialNerve (Object A)) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction
          (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}) i)) ≫ evaluationNerveFamily A =
      EnrichedParameterCylinder.nervePair (C := Object A) K ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (restrictedCylinderEnriched A i) := by
  rw [evaluationNerveFamily, ← Category.assoc, EnrichedParameterCylinder.nervePair_restriction,
    Category.assoc, evaluationCylinderInfinityMap_restriction]
  rfl

end CotensorCompatible

/-- 元の Sp 上の二変数の評価も、制限された元の円柱の評価へ厳密に制限される。 -/
lemma nativeCotensorEvaluationFamily_restriction (A : PointedSimplicialSet.{u})
    {K : SSet.{u}} (i : K ⟶ A.right) :
    (𝟙 Sp.{u} ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction
        (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}) i)) ≫ nativeCotensorEvaluationFamily A =
      ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 _) ≫
        EnrichedParameterCylinder.nervePair (C := CotensorCompatible.Object A) K ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (CotensorCompatible.restrictedCylinderEnriched A i) := by
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction
    (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}) i)
  have h :
      (𝟙 Sp.{u} ⊗ₘ r) ≫ ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 _) =
      ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 _) ≫
        (𝟙 (SimplicialNerve (CotensorCompatible.Object A)) ⊗ₘ r) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [nativeCotensorEvaluationFamily, ← Category.assoc, h, Category.assoc,
    CotensorCompatible.evaluationNerveFamily_restriction]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
