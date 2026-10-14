module

public import SerrePositivity.BhattScholze.DeltaRing

/-! # 長さ2のWitt環の単元判定

δ局所化のW₂切断を延長するためのBS専用補題。
第0座標と第1ghost成分が単元なら、明示的な逆元を構成する。
基底のp正則性や標数pは仮定しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- W₂の単元は第0座標と第1ghost成分が単元であることと同値。 -/
theorem wittTwo_isUnit_iff (x : WittTwo p A) :
    IsUnit x ↔ IsUnit (x.coeff 0) ∧ IsUnit (wittTwoFrobenius p A x) := by
  constructor
  · intro hx
    exact ⟨by simpa using hx.map (wittTwoProjection p A), hx.map (wittTwoFrobenius p A)⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let y : WittTwo p A := TruncatedWittVector.mk p (fun i ↦
      if i = 0 then (↑a⁻¹ : A) else -x.coeff 1 * (↑a⁻¹ : A) ^ p * (↑b⁻¹ : A))
    have hxy : x * y = 1 := by
      apply TruncatedWittVector.ext
      intro i
      fin_cases i
      · change (x.out * y.out).coeff 0 = (1 : WittVector p A).coeff 0
        rw [WittVector.mul_coeff_zero, WittVector.one_coeff_zero]
        change x.coeff 0 * (↑a⁻¹ : A) = 1
        rw [← ha, Units.mul_inv]
      · change (x.out * y.out).coeff 1 = (1 : WittVector p A).coeff 1
        rw [witt_mul_coeff_one, WittVector.one_coeff_eq_of_pos p A 1 (by decide)]
        change x.coeff 0 ^ p * (-x.coeff 1 * (↑a⁻¹ : A) ^ p * (↑b⁻¹ : A)) +
          x.coeff 1 * (↑a⁻¹ : A) ^ p +
          (p : A) * x.coeff 1 * (-x.coeff 1 * (↑a⁻¹ : A) ^ p * (↑b⁻¹ : A)) = 0
        have hghost : x.coeff 0 ^ p + (p : A) * x.coeff 1 = (b : A) :=
          (wittTwoFrobenius_apply p A x).symm.trans hb.symm
        calc
          _ = x.coeff 1 * (↑a⁻¹ : A) ^ p *
            (1 - (x.coeff 0 ^ p + (p : A) * x.coeff 1) * (↑b⁻¹ : A)) := by ring
          _ = 0 := by rw [hghost, Units.mul_inv]; ring
    exact ⟨⟨x, y, hxy, by simpa [mul_comm] using hxy⟩, rfl⟩

end SerrePositivity.BhattScholze
