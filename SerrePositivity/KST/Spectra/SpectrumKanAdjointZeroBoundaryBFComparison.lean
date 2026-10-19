module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointZeroBoundaryRectification
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterBFComparison

/-!
概要：零境界を保持した元の全 Hom の Kan 随伴比較を、同じ零境界を保って BF 模型へ持ち上げる。
方針：元の BF 射影への後合成の相対 RLP に、構成済みの零境界の全列比較を入力する。
規約：全パラメータの射影式と境界を厳密に保持。使われ方：基点つき球面族の BF 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right] (hzero : j ≫ φ = 0)

def kanAdjointZeroBoundaryBFLift :
    { l : A ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence //
      j ≫ l = 0 ∧ l ≫ pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
        kanAdjointZeroBoundaryComparison X Y φ j hzero } :=
  pointedPostRelativeLift X (OmegaSpectrum.signedLoopProjection Y)
    (signedLoopProjection_level_rlp Y) j 0 (kanAdjointZeroBoundaryComparison X Y φ j hzero)
    (by rw [zero_comp, kanAdjointZeroBoundaryComparison_boundary])

/-- 元の零境界の全パラメータ族から構成する、実際の BF loop 模型への零境界の比較。 -/
def kanAdjointZeroBoundaryBFComparison :
    A ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence :=
  (kanAdjointZeroBoundaryBFLift X Y φ j hzero).val

/-- BF への持ち上げでも、元の指定部分で零であることを全列で厳密に保持する。 -/
lemma kanAdjointZeroBoundaryBFComparison_boundary :
    j ≫ kanAdjointZeroBoundaryBFComparison X Y φ j hzero = 0 :=
  (kanAdjointZeroBoundaryBFLift X Y φ j hzero).property.1

/-- BF 射影へ戻すと、元の零境界を保持して厳密化した族そのものになる。 -/
@[reassoc]
lemma kanAdjointZeroBoundaryBFComparison_projection :
    kanAdjointZeroBoundaryBFComparison X Y φ j hzero ≫
      pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
      kanAdjointZeroBoundaryComparison X Y φ j hzero :=
  (kanAdjointZeroBoundaryBFLift X Y φ j hzero).property.2

/-- 各段の BF 射影座標も、元の同じ零境界の厳密化した座標と厳密に一致。 -/
lemma kanAdjointZeroBoundaryBFComparison_projected_evaluation (n : ℕ) :
    (kanAdjointZeroBoundaryBFComparison X Y φ j hzero ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
      PointedObject.basedHomMap (X.level n).space
        ((OmegaSpectrum.signedLoopProjection Y).app n) =
      kanAdjointZeroBoundaryComparison X Y φ j hzero ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n := by
  rw [Category.assoc, ← pointedPost_evaluation, ← Category.assoc,
    kanAdjointZeroBoundaryBFComparison_projection]

/-- BF 射影後の各段の成分は、元の族を元の Kan 随伴へ後合成した族の成分。 -/
lemma kanAdjointZeroBoundaryBFComparison_projected_component (n : ℕ) :
    PointedMapping.componentOf ((kanAdjointZeroBoundaryBFComparison X Y φ j hzero ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
      PointedObject.basedHomMap (X.level n).space
        ((OmegaSpectrum.signedLoopProjection Y).app n)) =
      PointedMapping.componentOf (φ ≫ kanAdjointParameterLeft X Y n) := by
  rw [kanAdjointZeroBoundaryBFComparison_projected_evaluation]
  exact kanAdjointZeroBoundaryComparison_evaluation_component X Y φ j hzero n

/-- 零段の元の Kan 随伴座標は、BF 射影後にも厳密に保持する。 -/
lemma kanAdjointZeroBoundaryBFComparison_projected_zero :
    (kanAdjointZeroBoundaryBFComparison X Y φ j hzero ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence 0) ≫
      PointedObject.basedHomMap (X.level 0).space
        ((OmegaSpectrum.signedLoopProjection Y).app 0) = φ ≫ kanAdjointParameterLeft X Y 0 := by
  rw [kanAdjointZeroBoundaryBFComparison_projected_evaluation]
  exact kanAdjointZeroBoundaryComparison_evaluation_zero X Y φ j hzero

end SerrePositivity.KST.Spectra.RawSpectrumMapping
