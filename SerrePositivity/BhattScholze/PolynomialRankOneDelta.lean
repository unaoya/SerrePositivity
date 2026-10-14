module

public import SerrePositivity.BhattScholze.DeltaSectionNaturality
public import SerrePositivity.BhattScholze.DeltaRankOne
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # rank 1変数を持つ補助多項式δ構造

基底δ構造を係数に延長し、各変数のδを零とする。
相対自由δ環の次座標へ移るδ構造とは区別する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (σ : Type v)

/-- 係数のδ切断と、rank 1変数のW₂座標による多項式切断。 -/
def polynomialRankOneDeltaSection (D : DeltaStructure p A) :
    MvPolynomial σ A →+* WittTwo p (MvPolynomial σ A) :=
  MvPolynomial.eval₂Hom ((wittTwoMap (p := p) MvPolynomial.C).comp D.sectionHom)
    (fun s => TruncatedWittVector.mk p (fun i => if i = 0 then MvPolynomial.X s else 0))

/-- 補助切断の第0座標は恒等射。 -/
theorem polynomialRankOneDeltaSection_projection (D : DeltaStructure p A) :
    (wittTwoProjection p (MvPolynomial σ A)).comp (polynomialRankOneDeltaSection σ D) =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, polynomialRankOneDeltaSection, MvPolynomial.eval₂Hom_C,
      wittTwoProjection_apply, wittTwoMap_coeff]
    rw [D.coeff_zero]
    rfl
  · intro s
    simp [polynomialRankOneDeltaSection]

/-- 変数がrank 1である補助多項式δ構造。 -/
def polynomialRankOneDeltaStructure (D : DeltaStructure p A) :
    DeltaStructure p (MvPolynomial σ A) where
  sectionHom := polynomialRankOneDeltaSection σ D
  coeff_zero := by
    intro f
    exact RingHom.congr_fun (polynomialRankOneDeltaSection_projection σ D) f

/-- 補助δ構造は基底係数上で元のδ構造に一致する。 -/
@[simp] theorem polynomialRankOneDeltaStructure_delta_C (D : DeltaStructure p A) (a : A) :
    (polynomialRankOneDeltaStructure σ D).delta (MvPolynomial.C a) =
      MvPolynomial.C (D.delta a) := by
  simp [DeltaStructure.delta, polynomialRankOneDeltaStructure, polynomialRankOneDeltaSection,
    MvPolynomial.eval₂Hom_C]

/-- 補助δ構造では各変数のδは零。 -/
@[simp] theorem polynomialRankOneDeltaStructure_delta_X (D : DeltaStructure p A) (s : σ) :
    (polynomialRankOneDeltaStructure σ D).delta (MvPolynomial.X s) = 0 := by
  simp [DeltaStructure.delta, polynomialRankOneDeltaStructure, polynomialRankOneDeltaSection,
    MvPolynomial.eval₂Hom_X']

/-- 補助多項式δ構造への係数射はδ射。 -/
theorem polynomialRankOneDeltaStructure_C_isDeltaHom (D : DeltaStructure p A) :
    D.IsDeltaHom (polynomialRankOneDeltaStructure σ D) MvPolynomial.C := by
  intro a
  exact (polynomialRankOneDeltaStructure_delta_C σ D a).symm

/-- rank 1変数のFrobenius像はp乗。 -/
@[simp] theorem polynomialRankOneDeltaStructure_frobenius_X (D : DeltaStructure p A) (s : σ) :
    (polynomialRankOneDeltaStructure σ D).frobeniusLift (MvPolynomial.X s) =
      MvPolynomial.X s ^ p := by
  rw [DeltaStructure.frobeniusLift_apply, polynomialRankOneDeltaStructure_delta_X,
    mul_zero, add_zero]

/-- rank 1変数のp乗もrank 1。 -/
@[simp] theorem polynomialRankOneDeltaStructure_delta_X_pow_prime (D : DeltaStructure p A) (s : σ) :
    (polynomialRankOneDeltaStructure σ D).delta (MvPolynomial.X s ^ p) = 0 := by
  have h := (polynomialRankOneDeltaStructure σ D).p_mul_delta_dvd_delta_pow (MvPolynomial.X s)
  rw [polynomialRankOneDeltaStructure_delta_X, mul_zero, zero_dvd_iff] at h
  exact h

end SerrePositivity.BhattScholze
