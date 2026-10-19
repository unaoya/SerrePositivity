module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointRelativeTracedComparison
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCanonicalBFComparison
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPostLifting
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterBFComparison

/-!
概要：実構造三角形を保持する Kan 随伴比較を、同じ非零境界の BF 模型へ持ち上げる。
方針：部分対象の全列族を先に持ち上げ、元の後合成の相対 RLP で全体を持ち上げる。
規約：境界と全列射影を厳密に保持。使われ方：元の BF 写像空間における相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)

variable [Mono j.right]

/-- 具体的な非零 BF 境界と元の全列射影を同時に保持した実際の持ち上げ。 -/
def kanAdjointRelativeTracedBFRelativeLift :
    { l : A ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence //
      j ≫ l = kanAdjointCanonicalBFBoundary X Y φ j ∧
      l ≫ pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
        kanAdjointRelativeTracedComparison X Y φ j } :=
  pointedPostRelativeLift X (OmegaSpectrum.signedLoopProjection Y)
    (signedLoopProjection_level_rlp Y) j (kanAdjointCanonicalBFBoundary X Y φ j)
    (kanAdjointRelativeTracedComparison X Y φ j)
    ((kanAdjointCanonicalBFBoundary_projection X Y φ j).trans
      (kanAdjointRelativeTracedComparison_boundary X Y φ j).symm)

/-- 元の非零境界を保持した Kan 随伴比較の、実際の BF 模型への比較。 -/
def kanAdjointRelativeTracedBFComparison :
    A ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence :=
  (kanAdjointRelativeTracedBFRelativeLift X Y φ j).val

/-- 全パラメータの BF 比較は、選んだ同じ非零 BF 境界へ厳密に制限される。 -/
lemma kanAdjointRelativeTracedBFComparison_boundary :
    j ≫ kanAdjointRelativeTracedBFComparison X Y φ j = kanAdjointCanonicalBFBoundary X Y φ j :=
  (kanAdjointRelativeTracedBFRelativeLift X Y φ j).property.1

/-- BF への持ち上げの元の射影は、具体的な非零境界を保つ比較そのもの。 -/
@[reassoc]
lemma kanAdjointRelativeTracedBFComparison_projection :
    kanAdjointRelativeTracedBFComparison X Y φ j ≫
      pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
        kanAdjointRelativeTracedComparison X Y φ j :=
  (kanAdjointRelativeTracedBFRelativeLift X Y φ j).property.2

/-- BF 射影後の段座標は、元の同じ全列の相対比較の座標へ厳密に戻る。 -/
lemma kanAdjointRelativeTracedBFComparison_projected_evaluation (n : ℕ) :
    (kanAdjointRelativeTracedBFComparison X Y φ j ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
        PointedObject.basedHomMap (X.level n).space
          ((OmegaSpectrum.signedLoopProjection Y).app n) =
      kanAdjointRelativeTracedComparison X Y φ j ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n := by
  rw [Category.assoc, ← pointedPost_evaluation, ← Category.assoc,
    kanAdjointRelativeTracedBFComparison_projection]

/-- BF 射影後の段座標にも、元の指定した非零境界ホモトピーを保持する。 -/
lemma kanAdjointRelativeTracedBFComparison_projected_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (φ ≫ kanAdjointParameterLeft X Y n).right
        ((kanAdjointRelativeTracedBFComparison X Y φ j ≫
          pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
          PointedObject.basedHomMap (X.level n).space
            ((OmegaSpectrum.signedLoopProjection Y).app n)).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        (kanAdjointTracedBoundaryHomotopy X Y φ j n).h := by
  rw [kanAdjointRelativeTracedBFComparison_projected_evaluation]
  exact kanAdjointRelativeTracedComparison_evaluation_homotopy X Y φ j n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
