module

public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic

/-!
概要：既存の区間環・剰余体の証明から、局所化と素イデアル商の完全係数の法則を抽出する。
方針：商へp乗根を写し、局所化では同じ素イデアルの外の分母の根を使う。
規約：既存構成と同じ係数・構造射を保持する。新たなNoether性・有限性の仮定を課さない。
使われ方：2iの係数移送L03・L04、BM18 Proposition 4.8(5)の普遍貼り合わせの係数。
-/

@[expose] public noncomputable section
universe u
open SerrePositivity
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 係数移送の法則L03：既存の完全係数の構成を同じ商・局所化へ渡す。 -/
theorem intervalCoefficient_primeQuotient_perfect (p : ℕ) [Fact p.Prime] {V : Type u}
    [CommRing V] [IsDomain V] [ValuationRing V] [PerfectRing V p]
    (hp : (p : V) = 0) (a : PrimeSpectrum V) :
    PerfectRing (V ⧸ a.asIdeal) p := by
  let Q := V ⧸ a.asIdeal
  have hQ : (p : Q) = 0 := by rw [← map_natCast (Ideal.Quotient.mk a.asIdeal), hp, map_zero]
  letI : CharP Q p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hQ
  apply PerfectRing.ofSurjective
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := (PerfectRing.bijective_frobenius (R := V) (p := p)).2 x
  change r ^ p = x at hr
  refine ⟨Ideal.Quotient.mk a.asIdeal r, ?_⟩
  change (Ideal.Quotient.mk a.asIdeal r) ^ p = Ideal.Quotient.mk a.asIdeal x
  rw [← map_pow, hr]

/-- 係数移送の法則L04：既存の完全係数の構成を同じ商・局所化へ渡す。 -/
theorem intervalCoefficient_primeLocalization_perfect (p : ℕ) [Fact p.Prime] {V : Type u}
    [CommRing V] [IsDomain V] [ValuationRing V] [PerfectRing V p]
    (hp : (p : V) = 0) (a : PrimeSpectrum V) :
    PerfectRing (Localization.AtPrime a.asIdeal) p := by
  let L := Localization.AtPrime a.asIdeal
  have hL : (p : L) = 0 := by rw [← map_natCast (algebraMap V L), hp, map_zero]
  letI : CharP L p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hL
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨v, s, rfl⟩ := IsLocalization.exists_mk'_eq a.asIdeal.primeCompl x
  obtain ⟨r, hr⟩ := (PerfectRing.bijective_frobenius (R := V) (p := p)).2 v
  obtain ⟨t, ht⟩ := (PerfectRing.bijective_frobenius (R := V) (p := p)).2 s.val
  change r ^ p = v at hr
  change t ^ p = s.val at ht
  have htM : t ∈ a.asIdeal.primeCompl := fun he ↦
    s.property (ht ▸ a.asIdeal.pow_mem_of_mem he p (Fact.out : p.Prime).pos)
  let t' : a.asIdeal.primeCompl := ⟨t, htM⟩
  have htp : t' ^ p = s := Subtype.ext ht
  exact ⟨IsLocalization.mk' L r t', by
    rw [frobenius_def, ← IsLocalization.mk'_pow, hr, htp]⟩

end SerrePositivity.AlgebraicGeometry.ArcRouteB
