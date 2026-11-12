module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitInvariance

/-!
概要：根基内の中心の変更は、商の Frobenius 順極限を変えない。
方針：実際の商の因子写像の核が nil であることと全射性を使う。
規約：比較は商の因子写像が誘導する射そのもの。
使われ方：導手の四角形を指定された中心の商へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A : Type u} [CommRing A]
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
variable {I J : Ideal A} (hIJ : I ≤ J) (hJI : J ≤ I.radical)

include hJI in
/-- 根基内で中心を大きくした商の因子写像の核は nil。 -/
theorem quotientFactor_kernel_nil (x : A ⧸ I)
    (hx : Ideal.Quotient.factor hIJ x = 0) : IsNilpotent x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hx
  obtain ⟨n, hn⟩ := hJI ha
  refine ⟨n, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

include hJI in
/-- 根基内で中心を変更する実際の商写像は、Frobenius 順極限上で全単射。 -/
theorem frobeniusQuotientFactor_bijective :
    Function.Bijective (frobeniusDirectLimitMap p hp
      (frobeniusQuotientPrimeCast p hA I) (frobeniusQuotientPrimeCast p hA J)
      (Ideal.Quotient.factor hIJ)) := by
  constructor
  · apply frobeniusDirectLimitMap_injective
    exact quotientFactor_kernel_nil hIJ hJI
  · apply frobeniusDirectLimitMap_surjective
    intro b
    obtain ⟨a, ha⟩ := Ideal.Quotient.factor_surjective hIJ b
    exact ⟨0, a, by simpa using ha⟩

end SerrePositivity.AlgebraicGeometry
