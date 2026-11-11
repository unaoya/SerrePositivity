module

public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationNerveFamily

/-!
概要：元の Sp 上の全対象・全高次単体での cotensor の評価の族。
方針：共通解像上の二変数の評価の源へ、元の射影同値の逆を合成する。
規約：左端は nativeCotensor に厳密一致し、右端は恒等関手と同型。
使われ方：円の評価と native loop の関手としての比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeCotensorEvaluationSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の Sp 上の二変数の coherent な普遍評価の族。 -/
def nativeCotensorEvaluationFamily (A : PointedSimplicialSet.{u}) :
    Sp.{u} ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}) ⟶ Sp.{u} :=
  ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 _) ≫
    CotensorCompatible.evaluationNerveFamily A

/-- 評価の族の左端は元の native cotensor 関手に厳密一致。 -/
lemma nativeCotensorEvaluationFamily_left (A : PointedSimplicialSet.{u}) :
    lift (𝟙 Sp.{u}) (SSet.const (EnrichedParameterCylinder.leftVertex.{u, u + 1} A.right)) ≫
      nativeCotensorEvaluationFamily A = nativeCotensor A := by
  have h :
      lift (𝟙 Sp.{u}) (SSet.const (EnrichedParameterCylinder.leftVertex.{u, u + 1} A.right)) ≫
        ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 _) =
      (CotensorCompatible.sourceInfinityEquivalence A).inv ≫
        lift (𝟙 (SimplicialNerve (CotensorCompatible.Object A)))
          (SSet.const (EnrichedParameterCylinder.leftVertex.{u, u + 1} A.right)) := rfl
  rw [nativeCotensorEvaluationFamily, ← Category.assoc, h, Category.assoc,
    CotensorCompatible.evaluationNerveFamily_left]
  rfl

/-- 評価の族の右端は元の射影同値の逆と射影の合成。 -/
lemma nativeCotensorEvaluationFamily_right (A : PointedSimplicialSet.{u}) :
    lift (𝟙 Sp.{u}) (SSet.const (EnrichedParameterCylinder.rightVertex.{u, u + 1} A.right)) ≫
        nativeCotensorEvaluationFamily A =
      (CotensorCompatible.sourceInfinityEquivalence A).inv ≫
        CotensorCompatible.sourceInfinityMap A := by
  have h :
      lift (𝟙 Sp.{u}) (SSet.const (EnrichedParameterCylinder.rightVertex.{u, u + 1} A.right)) ≫
        ((CotensorCompatible.sourceInfinityEquivalence A).inv ⊗ₘ 𝟙 _) =
      (CotensorCompatible.sourceInfinityEquivalence A).inv ≫
        lift (𝟙 (SimplicialNerve (CotensorCompatible.Object A)))
          (SSet.const (EnrichedParameterCylinder.rightVertex.{u, u + 1} A.right)) := rfl
  rw [nativeCotensorEvaluationFamily, ← Category.assoc, h, Category.assoc,
    CotensorCompatible.evaluationNerveFamily_right]

/-- 評価の族の右端は恒等関手と実際に関手同型。 -/
def nativeCotensorEvaluationFamily_rightIso (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift (𝟙 Sp.{u}) (SSet.const (EnrichedParameterCylinder.rightVertex.{u, u + 1} A.right)) ≫
        nativeCotensorEvaluationFamily A) (𝟙 Sp.{u}) := by
  rw [nativeCotensorEvaluationFamily_right]
  exact (CotensorCompatible.sourceInfinityEquivalence A).invHomIso

end SerrePositivity.KST.Spectra.OmegaSpectrum
