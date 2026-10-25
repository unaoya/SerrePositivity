module

public import SerrePositivity.BhattScholze.Delta.PerfectDeltaFrobenius
public import SerrePositivity.BhattScholze.Prism.PrismaticPowerResidueNilpotent

/-! # 完全係数δ環のFrobenius各段における正確なprism係数商 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A)

/-- pを消す任意の通常射の下で、実Frobenius反復はpⁿ乗として作用する。 -/
theorem map_frobeniusLift_iterate_of_map_p_eq_zero {T : Type v} [CommRing T]
    (f : A →+* T) (hp : f (p : A) = 0) (x : A) (n : ℕ) :
    f ((D.frobeniusLift ^ n) x) = f x ^ (p ^ n) := by
  change f ((D.frobeniusLift : A → A)^[n] x) = _
  induction n with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  | succ n ih =>
      rw [Function.iterate_succ_apply', D.map_frobeniusLift_of_map_p_eq_zero f hp, ih,
        Nat.pow_succ, pow_mul]

/-- Frobenius反復で動かした生成元の実(p,d)イデアルは、元の生成元のpⁿ冪のもの。 -/
theorem frobeniusPrismaticResidueIdeal_eq (d : A) (n : ℕ) :
    Ideal.span {(p : A), (D.frobeniusLift ^ n) d} =
      Ideal.span {(p : A), d ^ (p ^ n)} := by
  have he (J : Ideal A) (hp : (p : A) ∈ J) :
      Ideal.Quotient.mk J ((D.frobeniusLift ^ n) d) =
        Ideal.Quotient.mk J (d ^ (p ^ n)) := by
    rw [map_pow]
    exact map_frobeniusLift_iterate_of_map_p_eq_zero D (Ideal.Quotient.mk J)
      (Ideal.Quotient.eq_zero_iff_mem.mpr hp) d n
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [he _ (Ideal.subset_span (by simp))]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← he _ (Ideal.subset_span (by simp))]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- 完全係数δ環の実φⁿが誘導する、移動した生成元を用いた商環同型。 -/
def perfectDeltaFrobeniusPrismaticResidueEquiv (hD : D.IsPerfect) (d : A) (n : ℕ) :
    (A ⧸ Ideal.span {(p : A), d}) ≃+*
      (A ⧸ Ideal.span {(p : A), (D.frobeniusLift ^ n) d}) :=
  Ideal.quotientEquiv _ _ (RingEquiv.ofBijective (D.frobeniusLift ^ n) (hD.iterate n))
    (by rw [Ideal.map_span, Set.image_pair, map_natCast]; rfl)

/-- 移動した生成元の商同型は、元環の標準φⁿ係数像を保つ。 -/
theorem perfectDeltaFrobeniusPrismaticResidueEquiv_mk
    (hD : D.IsPerfect) (d : A) (n : ℕ) (x : A) :
    perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n
      (Ideal.Quotient.mk (Ideal.span {(p : A), d}) x) =
        Ideal.Quotient.mk _ ((D.frobeniusLift ^ n) x) := rfl

/-- 同じ実φⁿの係数商を、G10に使う正確なA/(p,d^(pⁿ))へ比較する。 -/
def perfectDeltaFrobeniusPowerResidueEquiv (hD : D.IsPerfect) (d : A) (n : ℕ) :
    (A ⧸ Ideal.span {(p : A), d}) ≃+*
      (A ⧸ Ideal.span {(p : A), d ^ (p ^ n)}) :=
  (perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n).trans
    (Ideal.quotEquivOfEq (frobeniusPrismaticResidueIdeal_eq D d n))

/-- 冪剰余への比較も、元環の実φⁿ係数像を保つ。 -/
theorem perfectDeltaFrobeniusPowerResidueEquiv_mk
    (hD : D.IsPerfect) (d : A) (n : ℕ) (x : A) :
    perfectDeltaFrobeniusPowerResidueEquiv D hD d n
      (Ideal.Quotient.mk (Ideal.span {(p : A), d}) x) =
        Ideal.Quotient.mk _ ((D.frobeniusLift ^ n) x) := by
  rw [perfectDeltaFrobeniusPowerResidueEquiv, RingEquiv.trans_apply,
    perfectDeltaFrobeniusPrismaticResidueEquiv_mk, Ideal.quotEquivOfEq_mk]

end SerrePositivity.BhattScholze
