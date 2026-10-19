module

public import SerrePositivity.KST.Spectra.PointedRelativeCofiberHomotopy
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointZeroBoundaryRelativeHomotopy

/-!
概要：零境界を保持した元の Kan 随伴比較を相対 cofiber へ降ろし、元の段座標と比較する。
方針：全列の降下は零境界の厳密式、座標の比較は相対ホモトピーの実際の降下を使う。
規約：各段の比較であり全列のホモトピーではない。使われ方：球面パラメータの写像類の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right] (hzero : j ≫ φ = 0)

/-- 元の零境界の族を cofiber へ降ろした全列の族。 -/
def kanAdjointCofiberInput : pointedCofiber j ⟶ pointedSpace X Y.toKanSequence :=
  pointedCofiberDescOfZero j φ hzero

/-- 元の零境界を保つ Kan 随伴比較を cofiber へ降ろした全列の族。 -/
def kanAdjointCofiberComparison :
    pointedCofiber j ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  pointedCofiberDescOfZero j (kanAdjointZeroBoundaryComparison X Y φ j hzero)
    (kanAdjointZeroBoundaryComparison_boundary X Y φ j hzero)

/-- cofiber 上の元の二つの段座標を結ぶ実際の基点固定ホモトピー。 -/
lemma kanAdjointCofiberComparison_evaluation_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (kanAdjointCofiberComparison X Y φ j hzero ≫
        pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n).right
        (kanAdjointCofiberInput X Y φ j hzero ≫ kanAdjointParameterLeft X Y n).right,
      (pointedCofiber j).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (kanAdjointParameterTarget X Y n).hom := by
  obtain ⟨H, hb, hr⟩ :=
    kanAdjointZeroBoundaryComparison_evaluation_relative_homotopy X Y φ j hzero n
  have hf : j ≫ (kanAdjointZeroBoundaryComparison X Y φ j hzero ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) = 0 := by
    rw [← Category.assoc, kanAdjointZeroBoundaryComparison_boundary, zero_comp]
  have hg : j ≫ (φ ≫ kanAdjointParameterLeft X Y n) = 0 := by
    rw [← Category.assoc, hzero, zero_comp]
  have h := PointedMapping.cofiberDesc_homotopy j hf hg H hb hr
  rw [pointedCofiberDescOfZero_comp, pointedCofiberDescOfZero_comp] at h
  exact h

/-- 同じ cofiber 上の実際の降下射の座標は、同じ写像成分を表す。 -/
lemma kanAdjointCofiberComparison_evaluation_component (n : ℕ) :
    PointedMapping.componentOf (kanAdjointCofiberComparison X Y φ j hzero ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n) =
    PointedMapping.componentOf (kanAdjointCofiberInput X Y φ j hzero ≫
      kanAdjointParameterLeft X Y n) := by
  obtain ⟨H, hb⟩ := kanAdjointCofiberComparison_evaluation_homotopy X Y φ j hzero n
  exact π₀.sound (PointedMapping.edgeOfHomotopy H hb)

/-- cofiber 上でも、零段の座標は厳密に元の Kan 随伴の座標。 -/
lemma kanAdjointCofiberComparison_evaluation_zero :
    kanAdjointCofiberComparison X Y φ j hzero ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) 0 =
    kanAdjointCofiberInput X Y φ j hzero ≫ kanAdjointParameterLeft X Y 0 := by
  apply pointedCofiber_hom_ext j
  simpa only [kanAdjointCofiberComparison, kanAdjointCofiberInput, ← Category.assoc,
    pointedCofiberProjection_descOfZero] using
    kanAdjointZeroBoundaryComparison_evaluation_zero X Y φ j hzero

/-- 元の BF 持ち上げを同じ cofiber へ降ろした全列の族。 -/
def kanAdjointCofiberBFComparison :
    pointedCofiber j ⟶ pointedSpace X (OmegaSpectrum.signedLoopModel Y).toKanSequence :=
  pointedCofiberDescOfZero j (kanAdjointZeroBoundaryBFComparison X Y φ j hzero)
    (kanAdjointZeroBoundaryBFComparison_boundary X Y φ j hzero)

/-- cofiber へ降ろした後も、元の BF 射影との厳密な比較式を保つ。 -/
@[reassoc]
lemma kanAdjointCofiberBFComparison_projection :
    kanAdjointCofiberBFComparison X Y φ j hzero ≫
      pointedPost X (OmegaSpectrum.signedLoopProjection Y) =
      kanAdjointCofiberComparison X Y φ j hzero := by
  apply pointedCofiber_hom_ext j
  simpa only [kanAdjointCofiberBFComparison, kanAdjointCofiberComparison,
    ← Category.assoc, pointedCofiberProjection_descOfZero] using
    kanAdjointZeroBoundaryBFComparison_projection X Y φ j hzero

/-- cofiber 上の BF 射影後の段座標は、元の厳密化の座標に一致する。 -/
lemma kanAdjointCofiberBFComparison_projected_evaluation (n : ℕ) :
    (kanAdjointCofiberBFComparison X Y φ j hzero ≫
      pointedEvaluation X (OmegaSpectrum.signedLoopModel Y).toKanSequence n) ≫
      PointedObject.basedHomMap (X.level n).space
        ((OmegaSpectrum.signedLoopProjection Y).app n) =
    kanAdjointCofiberComparison X Y φ j hzero ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n := by
  rw [Category.assoc, ← pointedPost_evaluation, ← Category.assoc,
    kanAdjointCofiberBFComparison_projection]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
