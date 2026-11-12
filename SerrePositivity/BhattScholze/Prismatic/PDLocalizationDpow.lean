module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Localization.Ideal

/-!
# 局所化した分冪の分数公式

## 概要
分冪イデアルの局所化に分数の分冪を定義し、表示によらないことを示す。

## 方針
γ_n(a/s)=γ_n(a)/s^n と置き、分数の等式を分母を払った等式へ戻して照合する。

## 規約
任意の乗法的集合の局所化を扱い、正則性や平坦性の仮定は追加しない。

## 使われ方
Berthelot I.1.7.1、III.4、Stacks 07HN。結晶厚化の主開局所化の分冪構造。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
variable {R : Type u} [CommRing R] (M : Submonoid R)
variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
variable {I : Ideal R} (δ : DividedPowers I)

/-- 同じ分数の二つの表示は、分冪の分数公式でも同じ値を与える。 -/
theorem dpowFraction_eq_of_eq (n : ℕ) {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (s t : M) (h : IsLocalization.mk' S a s = IsLocalization.mk' S b t) :
    IsLocalization.mk' S (δ.dpow n a) (s ^ n) =
      IsLocalization.mk' S (δ.dpow n b) (t ^ n) := by
  obtain ⟨c, hc⟩ := (IsLocalization.eq (M := M) (S := S)).mp h
  simp only [← mul_assoc] at hc
  have hγ := congrArg (δ.dpow n) hc
  rw [δ.dpow_mul ha, δ.dpow_mul hb] at hγ
  apply IsLocalization.mk'_eq_iff_eq.mpr
  apply (IsLocalization.eq_iff_exists M S).mpr
  refine ⟨c ^ n, ?_⟩
  simpa only [SubmonoidClass.coe_pow, mul_pow, mul_assoc] using hγ

/-- 分冪イデアルの元を分母で割っても、局所化したイデアルに属する。 -/
theorem fraction_mem {a : R} (ha : a ∈ I) (s : M) :
    IsLocalization.mk' S a s ∈ I.map (algebraMap R S) := by
  apply (IsLocalization.mem_map_algebraMap_iff M S).mpr
  exact ⟨(⟨a, ha⟩, s), IsLocalization.mk'_spec S a s⟩

private def representation (z : S) (hz : z ∈ I.map (algebraMap R S)) : I × M :=
  ((IsLocalization.mem_map_algebraMap_iff M S).mp hz).choose

private theorem representation_spec (z : S) (hz : z ∈ I.map (algebraMap R S)) :
    IsLocalization.mk' S ((representation M S z hz).1 : R) (representation M S z hz).2 = z :=
  (IsLocalization.eq_mk'_iff_mul_eq.mpr
    ((IsLocalization.mem_map_algebraMap_iff M S).mp hz).choose_spec).symm

open Classical in
/-- 局所化したイデアルの上では分数公式、外では零とする分冪演算。 -/
def localizationDpow (n : ℕ) (z : S) : S :=
  if hz : z ∈ I.map (algebraMap R S) then
    IsLocalization.mk' S (δ.dpow n ((representation M S z hz).1 : R))
      ((representation M S z hz).2 ^ n)
  else 0

/-- 局所化した分冪演算の、任意のイデアルの分数表示での値。 -/
theorem localizationDpow_mk (n : ℕ) {a : R} (ha : a ∈ I) (s : M) :
    localizationDpow M S δ n (IsLocalization.mk' S a s) =
      IsLocalization.mk' S (δ.dpow n a) (s ^ n) := by
  classical
  unfold localizationDpow
  rw [dite_eq_left (fraction_mem M S ha s)]
  apply dpowFraction_eq_of_eq M S δ n (representation M S _ _).1.property ha
  exact representation_spec M S _ _

end SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
