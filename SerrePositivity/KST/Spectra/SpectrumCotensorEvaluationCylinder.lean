module

public import SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinderEndpoints
public import SerrePositivity.KST.Spectra.SpectrumCotensorUnpointedEvaluation
public import SerrePositivity.KST.Spectra.SpectrumNativeCotensor

/-!
概要：BF cotensor の普遍評価のパラメータ付き円柱を元の Sp へ送る。
方針：基点を忘れた豊穣自然変換から円柱の豊穣関手を作り、coherent nerve を取る。
規約：両端の射影と元の評価パラメータを保持する。
使われ方：円の評価から loop 四角形の族を取り出す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance evaluationCylinderSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の cotensor の普遍評価を保持する、パラメータ付き円柱の豊穣関手。 -/
def evaluationCylinderEnriched (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor SSet.{u} (EnrichedParameterCylinder.Object A.right (Object A))
      OmegaSpectrum.{u} :=
  EnrichedParameterCylinder.evaluationFunctor A.right (cotensorEnriched A) (sourceEnriched A)
    (unpointedGradedEvaluation A)

/-- 普遍評価の円柱を元の Sp に送る実際の coherent な図式。 -/
def evaluationCylinderInfinityMap (A : PointedSimplicialSet.{u}) :
    SimplicialNerve (EnrichedParameterCylinder.Object A.right (Object A)) ⟶ Sp.{u} :=
  coherentNerveMap (evaluationCylinderEnriched A)

/-- 評価の円柱の左端は、元の cotensor 側の射影そのもの。 -/
lemma evaluationCylinderInfinityMap_left (A : PointedSimplicialSet.{u}) :
    coherentNerveMap (EnrichedParameterCylinder.leftInclusion (C := Object A) A.right) ≫
        evaluationCylinderInfinityMap A = cotensorInfinityMap A := by
  rw [evaluationCylinderInfinityMap, ← coherentNerveMap_comp]
  change coherentNerveMap
    ((EnrichedParameterCylinder.leftInclusion A.right).comp SSet
      (EnrichedParameterCylinder.evaluationFunctor A.right (cotensorEnriched A)
        (sourceEnriched A) (unpointedGradedEvaluation A))) = _
  rw [EnrichedParameterCylinder.evaluationFunctor_left]
  rfl

/-- 評価の円柱の右端は、元の BF 対象への射影そのもの。 -/
lemma evaluationCylinderInfinityMap_right (A : PointedSimplicialSet.{u}) :
    coherentNerveMap (EnrichedParameterCylinder.rightInclusion (C := Object A) A.right) ≫
        evaluationCylinderInfinityMap A = sourceInfinityMap A := by
  rw [evaluationCylinderInfinityMap, ← coherentNerveMap_comp]
  change coherentNerveMap
    ((EnrichedParameterCylinder.rightInclusion A.right).comp SSet
      (EnrichedParameterCylinder.evaluationFunctor A.right (cotensorEnriched A)
        (sourceEnriched A) (unpointedGradedEvaluation A))) = _
  rw [EnrichedParameterCylinder.evaluationFunctor_right]
  rfl

/-- 同じ対象の二つの端の間の評価は、元の普遍評価を厳密に回収する。 -/
lemma evaluationCylinder_cross (A : PointedSimplicialSet.{u}) (X : Object A) :
    EnrichedParameterCylinder.crossIdentity A.right X ≫
      (evaluationCylinderEnriched A).map
        ((EnrichedParameterCylinder.leftInclusion A.right).obj X)
        ((EnrichedParameterCylinder.rightInclusion A.right).obj X) =
      (cotensorEvaluation A X.val).right :=
  EnrichedParameterCylinder.crossIdentity_evaluation A.right (cotensorEnriched A)
    (sourceEnriched A) (unpointedGradedEvaluation A) X

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
