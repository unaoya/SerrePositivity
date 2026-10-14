module

public import SerrePositivity.BhattScholze.RelativeFreeFiniteDeltaStep

/-! # 任意有限δ計算の加法・積とFrobenius公式

既存のWitt係数公式を有限W₂計算射へ適用する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 有限包含の合成は元の相対自由環への標準包含。 -/
theorem relativeFreeFiniteStepInclusion_comp_initial :
    (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A).toRingHom.comp
      (relativeFreeFiniteStepInclusion (A := A) N σ) =
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [relativeFreeFiniteInitialPolynomialMap, relativeFreeFiniteStepInclusion]
  · intro z
    obtain ⟨s, i⟩ := z
    simp [relativeFreeFiniteInitialPolynomialMap, relativeFreeFiniteStepInclusion]

/-- 有限計算射の第0座標の点ごとの式。 -/
@[simp] theorem relativeFreeFiniteDeltaStepSection_coeff_zero (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeFiniteDeltaStepSection N σ D f).coeff 0 = relativeFreeFiniteStepInclusion N σ f :=
  RingHom.congr_fun (relativeFreeFiniteDeltaStepSection_projection N σ D) f

/-- 有限δ計算は零を零へ送る。 -/
@[simp] theorem relativeFreeFiniteDeltaStep_zero (D : DeltaStructure p A) :
    relativeFreeFiniteDeltaStep N σ D 0 = 0 := by
  change (relativeFreeFiniteDeltaStepSection N σ D 0).coeff 1 = 0
  rw [map_zero]
  change (0 : WittVector p (MvPolynomial (σ × Fin (N + 2)) A)).coeff 1 = 0
  exact WittVector.zero_coeff (R := MvPolynomial (σ × Fin (N + 2)) A) p 1

/-- 有限δ計算は単位元を零へ送る。 -/
@[simp] theorem relativeFreeFiniteDeltaStep_one (D : DeltaStructure p A) :
    relativeFreeFiniteDeltaStep N σ D 1 = 0 := by
  change (relativeFreeFiniteDeltaStepSection N σ D 1).coeff 1 = 0
  rw [map_one]
  change (1 : WittVector p (MvPolynomial (σ × Fin (N + 2)) A)).coeff 1 = 0
  exact WittVector.one_coeff_eq_of_pos p _ 1 (by decide)

/-- 任意有限段のδ加法公式。補正項の入力は次の段への標準包含。 -/
theorem relativeFreeFiniteDeltaStep_add (D : DeltaStructure p A)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaStep N σ D (f + g) =
      relativeFreeFiniteDeltaStep N σ D f + relativeFreeFiniteDeltaStep N σ D g +
        (WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ f) +
          WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ g)).coeff 1 := by
  change (relativeFreeFiniteDeltaStepSection N σ D (f + g)).coeff 1 = _
  rw [map_add]
  change ((relativeFreeFiniteDeltaStepSection N σ D f).out +
    (relativeFreeFiniteDeltaStepSection N σ D g).out).coeff 1 = _
  rw [witt_add_coeff_one]
  simp [TruncatedWittVector.out, relativeFreeFiniteDeltaStep]

/-- 任意有限段のδ積公式。pねじれの除去は使わない。 -/
theorem relativeFreeFiniteDeltaStep_mul (D : DeltaStructure p A)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaStep N σ D (f * g) =
      (relativeFreeFiniteStepInclusion N σ f) ^ p * relativeFreeFiniteDeltaStep N σ D g +
        relativeFreeFiniteDeltaStep N σ D f * (relativeFreeFiniteStepInclusion N σ g) ^ p +
        (p : MvPolynomial (σ × Fin (N + 2)) A) *
          relativeFreeFiniteDeltaStep N σ D f * relativeFreeFiniteDeltaStep N σ D g := by
  change (relativeFreeFiniteDeltaStepSection N σ D (f * g)).coeff 1 = _
  rw [map_mul]
  change ((relativeFreeFiniteDeltaStepSection N σ D f).out *
    (relativeFreeFiniteDeltaStepSection N σ D g).out).coeff 1 = _
  rw [witt_mul_coeff_one]
  simp [TruncatedWittVector.out, relativeFreeFiniteDeltaStep]

/-- 有限W₂計算射から得る一段大きい環へのFrobenius射。 -/
def relativeFreeFiniteFrobeniusStep (D : DeltaStructure p A) :
    MvPolynomial (σ × Fin (N + 1)) A →+* MvPolynomial (σ × Fin (N + 2)) A :=
  (wittTwoFrobenius p (MvPolynomial (σ × Fin (N + 2)) A)).comp
    (relativeFreeFiniteDeltaStepSection N σ D)

/-- 有限Frobenius射の具体的な式。 -/
@[simp] theorem relativeFreeFiniteFrobeniusStep_apply (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteFrobeniusStep N σ D f = (relativeFreeFiniteStepInclusion N σ f) ^ p +
      (p : MvPolynomial (σ × Fin (N + 2)) A) * relativeFreeFiniteDeltaStep N σ D f := by
  simp [relativeFreeFiniteFrobeniusStep, relativeFreeFiniteDeltaStep]

/-- 有限Frobenius計算の像は、相対自由δ環の実際のFrobenius像。 -/
theorem relativeFreeFiniteFrobeniusStep_image (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteInitialPolynomialMap (N + 2) σ A (relativeFreeFiniteFrobeniusStep N σ D f) =
      (relativeFreeDeltaStructure σ D).frobeniusLift
        (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) := by
  rw [relativeFreeFiniteFrobeniusStep_apply, map_add, map_pow, map_mul, map_natCast,
    ← relativeFreeFiniteDeltaStep_delta_image, DeltaStructure.frobeniusLift_apply]
  have he := RingHom.congr_fun (relativeFreeFiniteStepInclusion_comp_initial (A := A) N σ) f
  rw [show relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
    (relativeFreeFiniteStepInclusion N σ f) =
      relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f from he]

end SerrePositivity.BhattScholze
