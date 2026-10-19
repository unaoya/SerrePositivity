module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCanonicalRelativeComparison
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPostLifting
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterBFComparison

/-!
概要：具体的な非零境界を保つ Kan 随伴比較を、同じ境界の BF 持ち上げを保って BF 模型へ移す。
方針：部分対象の全列族を先に持ち上げ、元の後合成の相対 RLP で全体を持ち上げる。
規約：境界と全列射影を厳密に保持。使われ方：元の BF 写像空間における相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)

/-- 帰納構成で選んだ非零境界を、同じ全列の射影を保って BF 模型へ持ち上げる。 -/
def kanAdjointCanonicalBFBoundary :
    B ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence :=
  pointedPostLift X (OmegaSpectrum.signedLoopProjection Y) (signedLoopProjection_level_rlp Y)
    (kanAdjointTracedBoundary X Y φ j)

/-- 境界の BF 持ち上げも、元の同じ帰納境界へ厳密に射影される。 -/
lemma kanAdjointCanonicalBFBoundary_projection :
    kanAdjointCanonicalBFBoundary X Y φ j ≫
      pointedPost X (OmegaSpectrum.signedLoopProjection Y) = kanAdjointTracedBoundary X Y φ j :=
  pointedPostLift_fac X (OmegaSpectrum.signedLoopProjection Y) (signedLoopProjection_level_rlp Y)
    (kanAdjointTracedBoundary X Y φ j)

variable [Mono j.right]

/-- 具体的な非零 BF 境界と元の全列射影を同時に保持した実際の持ち上げ。 -/
def kanAdjointCanonicalBFRelativeLift :
    { l : A ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence //
      j ≫ l = kanAdjointCanonicalBFBoundary X Y φ j ∧
      l ≫ pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
        kanAdjointCanonicalRelativeComparison X Y φ j } :=
  pointedPostRelativeLift X (OmegaSpectrum.signedLoopProjection Y)
    (signedLoopProjection_level_rlp Y) j (kanAdjointCanonicalBFBoundary X Y φ j)
    (kanAdjointCanonicalRelativeComparison X Y φ j)
    ((kanAdjointCanonicalBFBoundary_projection X Y φ j).trans
      (kanAdjointCanonicalRelativeComparison_boundary X Y φ j).symm)

/-- 元の非零境界を保持した Kan 随伴比較の、実際の BF 模型への比較。 -/
def kanAdjointCanonicalBFComparison :
    A ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence :=
  (kanAdjointCanonicalBFRelativeLift X Y φ j).val

/-- 全パラメータの BF 比較は、選んだ同じ非零 BF 境界へ厳密に制限される。 -/
lemma kanAdjointCanonicalBFComparison_boundary :
    j ≫ kanAdjointCanonicalBFComparison X Y φ j = kanAdjointCanonicalBFBoundary X Y φ j :=
  (kanAdjointCanonicalBFRelativeLift X Y φ j).property.1

/-- BF への持ち上げの元の射影は、具体的な非零境界を保つ比較そのもの。 -/
@[reassoc]
lemma kanAdjointCanonicalBFComparison_projection :
    kanAdjointCanonicalBFComparison X Y φ j ≫
      pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
        kanAdjointCanonicalRelativeComparison X Y φ j :=
  (kanAdjointCanonicalBFRelativeLift X Y φ j).property.2

/-- BF 射影後の段座標は、元の同じ全列の相対比較の座標へ厳密に戻る。 -/
lemma kanAdjointCanonicalBFComparison_projected_evaluation (n : ℕ) :
    (kanAdjointCanonicalBFComparison X Y φ j ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
        PointedObject.basedHomMap (X.level n).space
          ((OmegaSpectrum.signedLoopProjection Y).app n) =
      kanAdjointCanonicalRelativeComparison X Y φ j ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n := by
  rw [Category.assoc, ← pointedPost_evaluation, ← Category.assoc,
    kanAdjointCanonicalBFComparison_projection]

/-- BF 射影後の段の成分も、元の Kan 随伴の同じ段座標の成分。 -/
lemma kanAdjointCanonicalBFComparison_projected_component (n : ℕ) :
    PointedMapping.componentOf ((kanAdjointCanonicalBFComparison X Y φ j ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
        PointedObject.basedHomMap (X.level n).space
          ((OmegaSpectrum.signedLoopProjection Y).app n)) =
      PointedMapping.componentOf (φ ≫ kanAdjointParameterLeft X Y n) := by
  rw [kanAdjointCanonicalBFComparison_projected_evaluation]
  exact kanAdjointCanonicalRelativeComparison_evaluation_component X Y φ j n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
