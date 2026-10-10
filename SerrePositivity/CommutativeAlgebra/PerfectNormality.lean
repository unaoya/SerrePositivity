module

public import SerrePositivity.CommutativeAlgebra.SeparableBaseChange
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.FieldTheory.Perfect

/-!
# 完全な純非分離整拡大の正規性

正規整域 `A` の整拡大 `S` が完全環で、分数体の拡大が純非分離なら、`S` も正規である。
分数体の整元の十分大きな Frobenius 冪を `Frac(A)` に戻し、`A` の正規性で `A` の元に戻す。
最後に `S` の完全性で根を取る。この証明は Noether 性を必要としない。
-/

public section
universe u
namespace SerrePositivity

/-- 完全整域の分数体も完全である。分子と分母の Frobenius 根を別々に取り、
その商を根として使う。Noether 性や有限生成性は必要ない。 -/
theorem perfectRing_fractionRing
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [ExpChar K p] [PerfectRing R p] : PerfectRing K p := by
  apply PerfectRing.ofSurjective K p
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R x
  obtain ⟨r, hr⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).surjective a
  obtain ⟨s, hs⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).surjective b
  refine ⟨algebraMap R K r / algebraMap R K s, ?_⟩
  change (algebraMap R K r / algebraMap R K s) ^ p = _
  change r ^ p = a at hr
  change s ^ p = b at hs
  rw [div_pow, ← map_pow, ← map_pow, hr, hs]

/-- 完全な純非分離整拡大は正規性を保つ。
整性の推移性により、元の環まで整方程式を降ろしてから Frobenius 冪を使う。 -/
theorem isIntegrallyClosed_of_perfect_of_purelyInseparable
    (A S K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing S] [IsDomain S] [Field K] [Field L]
    [Algebra A S] [Algebra.IsIntegral A S]
    [Algebra A K] [IsFractionRing A K] [Algebra S L] [IsFractionRing S L]
    [Algebra A L] [Algebra K L] [IsScalarTower A S L] [IsScalarTower A K L]
    (p : ℕ) [ExpChar K p] [ExpChar L p] [PerfectRing S p]
    [IsPurelyInseparable K L] : IsIntegrallyClosed S := by
  apply (isIntegrallyClosed_iff L).mpr
  intro x hx
  have hxA : IsIntegral A x := isIntegral_trans x hx
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem K p x
  have hyA : IsIntegral A y := by
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L)
      (algebraMap K L).injective).mp
    change IsIntegral A (algebraMap K L y)
    rw [hy]
    exact hxA.pow _
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hyA
  obtain ⟨s, hs⟩ := (PerfectRing.bijective_frobenius
    (R := S) (p := p ^ n)).surjective (algebraMap A S a)
  refine ⟨s, iterateFrobenius_inj L p n ?_⟩
  change algebraMap S L s ^ (p ^ n) = x ^ (p ^ n)
  change s ^ (p ^ n) = algebraMap A S a at hs
  rw [← map_pow, hs, ← IsScalarTower.algebraMap_apply A S L,
    IsScalarTower.algebraMap_apply A K L, ha, hy]

end SerrePositivity
