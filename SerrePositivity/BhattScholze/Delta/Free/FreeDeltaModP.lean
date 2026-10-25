module

public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # B4-6：自由整数δ環のmod pの具体的表示

係数を素数体へ写す標準射の核を(p)と計算し、標準商同型を構成する。
Frobeniusの平坦性への接続に使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 自由整数δ環の係数を素数体へ写す標準射。 -/
def freeDeltaModPMap : FreeDeltaRing σ →+* MvPolynomial (σ × ℕ) (ZMod p) :=
  MvPolynomial.map (Int.castRingHom (ZMod p))

/-- 標準係数射は全射。 -/
theorem freeDeltaModPMap_surjective : Function.Surjective (freeDeltaModPMap p σ) :=
  MvPolynomial.map_surjective _ (ZMod.intCast_surjective (n := p))

/-- 標準係数射の核はpの単項イデアル。 -/
theorem freeDeltaModPMap_ker : RingHom.ker (freeDeltaModPMap p σ) =
    Ideal.span {(p : FreeDeltaRing σ)} := by
  apply le_antisymm
  · intro x hx
    change freeDeltaModPMap p σ x = 0 at hx
    have hcoeff (d : (σ × ℕ) →₀ ℕ) : (p : ℤ) ∣ x.coeff d := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      have he := congrArg (fun y : MvPolynomial (σ × ℕ) (ZMod p) ↦ y.coeff d) hx
      simpa only [freeDeltaModPMap, MvPolynomial.coeff_map, Int.coe_castRingHom,
        AddMonoidAlgebra.coeff_zero, Pi.zero_apply, Finsupp.zero_apply] using he
    let g : FreeDeltaRing σ := (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm
      (((AddMonoidAlgebra.coeffLinearEquiv ℤ) x).mapRange (fun c ↦ c / (p : ℤ)) (by simp))
    have hxg : x = (p : FreeDeltaRing σ) * g := by
      apply MvPolynomial.ext
      intro d
      change x.coeff d = (MvPolynomial.C (p : ℤ) * g).coeff d
      rw [MvPolynomial.coeff_C_mul]
      change x.coeff d = (p : ℤ) * (x.coeff d / (p : ℤ))
      exact (Int.mul_ediv_cancel' (hcoeff d)).symm
    rw [hxg]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    change freeDeltaModPMap p σ (p : FreeDeltaRing σ) = 0
    rw [map_natCast, CharP.cast_eq_zero]

/-- 自由整数δ環のmod pと素数体係数多項式環の標準商同型。 -/
def freeDeltaModPEquiv :
    (FreeDeltaRing σ ⧸ Ideal.span {(p : FreeDeltaRing σ)}) ≃+*
      MvPolynomial (σ × ℕ) (ZMod p) :=
  (Ideal.quotEquivOfEq (freeDeltaModPMap_ker p σ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (freeDeltaModPMap_surjective p σ))

/-- 標準商同型の代表元上の式。 -/
@[simp] theorem freeDeltaModPEquiv_mk (x : FreeDeltaRing σ) :
    freeDeltaModPEquiv p σ (Ideal.Quotient.mk _ x) = freeDeltaModPMap p σ x := rfl

/-- 標準商同型は自由δ環のFrobeniusのmod p式を素数体のFrobeniusへ移す。 -/
theorem freeDeltaModPEquiv_frobenius_mk (x : FreeDeltaRing σ) :
    freeDeltaModPEquiv p σ (Ideal.Quotient.mk _ (freeDeltaFrobenius p σ x)) =
      (freeDeltaModPEquiv p σ (Ideal.Quotient.mk _ x)) ^ p := by
  rw [freeDeltaFrobenius_mod_p, map_pow]

end SerrePositivity.BhattScholze
