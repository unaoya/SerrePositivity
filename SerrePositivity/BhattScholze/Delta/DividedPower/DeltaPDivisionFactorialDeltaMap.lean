module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialMap

/-! # 実階乗部分環の誘導射のδ射性

既存δ局所化の普遍性と、制限したδ作用の具体式を使用する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}

/-- 基底δ射から誘導された実p局所化写像はδ射。 -/
theorem pDivisionFactorialAwayMap_isDeltaHom (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (deltaPDivisionAwayStructure D).IsDeltaHom (deltaPDivisionAwayStructure E)
      (pDivisionFactorialAwayMap p f) := by
  let Aₚ := Localization.Away (p : A)
  let Bₚ := Localization.Away (p : B)
  let f₀ := (algebraMap B Bₚ).comp f
  have hu : ∀ s : Submonoid.powers (p : A), IsUnit (f₀ s) := by
    intro s
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : A) (p : A)).mp s.property
    rw [← hn, map_pow, map_natCast]
    have hp : IsUnit (p : Bₚ) := by
      simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (S := Bₚ) (p : B)
    exact hp.pow n
  obtain ⟨g, hg, _⟩ := D.existsUnique_localization_lift (Submonoid.powers (p : A)) Aₚ
    D.powers_p_frobenius_stable (deltaPDivisionAwayStructure E) f₀
    ((deltaPDivisionAwayStructure_base_isDeltaHom E).comp hf) hu
  have he : g = pDivisionFactorialAwayMap p f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : A))
    apply RingHom.ext
    intro a
    change g (algebraMap A Aₚ a) = pDivisionFactorialAwayMap p f (algebraMap A Aₚ a)
    have h := RingHom.congr_fun hg.1 a
    exact h.trans (pDivisionFactorialAwayMap_coeff f a).symm
  exact he ▸ hg.2

/-- 基底δ射に沿う実階乗部分環射も、既存δ作用の制限を保つ。 -/
theorem pDivisionFactorialMap_isDeltaHom
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B)) (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) (y : σ → A) :
    (pDivisionFactorialDelta hA D y).IsDeltaHom
      (pDivisionFactorialDelta hB E (fun s ↦ f (y s))) (pDivisionFactorialMap hA f y) := by
  intro a
  apply Subtype.ext
  exact pDivisionFactorialAwayMap_isDeltaHom D E f hf (a : Localization.Away (p : A))

end SerrePositivity.BhattScholze
