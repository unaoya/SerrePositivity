module

public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderNervePair
public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationCylinder

/-!
概要：cotensor の普遍評価を、共通解像の nerve と二対象のパラメータ図式の二変数の族にする。
方針：円柱の nerve の pairing と元の評価図式を合成する。
規約：両端の射影を厳密に保持する。使われ方：元の Sp 上の評価の族への移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance evaluationNerveFamilySpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の cotensor の普遍評価の、実際の二変数の coherent な族。 -/
def evaluationNerveFamily (A : PointedSimplicialSet.{u}) :
    SimplicialNerve (Object A) ⊗
        SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}) ⟶ Sp.{u} :=
  EnrichedParameterCylinder.nervePair A.right ≫ evaluationCylinderInfinityMap A

/-- 二変数の評価の左端は元の cotensor 射影そのもの。 -/
lemma evaluationNerveFamily_left (A : PointedSimplicialSet.{u}) :
    lift (𝟙 (SimplicialNerve (Object A)))
        (SSet.const (EnrichedParameterCylinder.leftVertex.{u, u + 1} A.right)) ≫
          evaluationNerveFamily A = cotensorInfinityMap A := by
  rw [evaluationNerveFamily, ← Category.assoc, EnrichedParameterCylinder.nervePair_left,
    evaluationCylinderInfinityMap_left]

/-- 二変数の評価の右端は元の BF 対象への射影そのもの。 -/
lemma evaluationNerveFamily_right (A : PointedSimplicialSet.{u}) :
    lift (𝟙 (SimplicialNerve (Object A)))
        (SSet.const (EnrichedParameterCylinder.rightVertex.{u, u + 1} A.right)) ≫
          evaluationNerveFamily A = sourceInfinityMap A := by
  rw [evaluationNerveFamily, ← Category.assoc, EnrichedParameterCylinder.nervePair_right,
    evaluationCylinderInfinityMap_right]

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
