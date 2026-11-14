module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDLocalizationDpow
import all SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDLocalizationDpow

/-!
# 局所化した分冪の基本恒等式

## 概要
分数公式から零次・一次・イデアルの保存・斉次性・同じ元の積と合成の公式を示す。

## 方針
局所化イデアルの各元をイデアルの分数に直し、元の分冪の恒等式を分母付きで写す。

## 規約
加法の公式は別ファイルで示す。

## 使われ方
Berthelot I.1.7.1、III.4。結晶厚化の主開局所化の分冪構造。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
variable {R : Type u} [CommRing R] (M : Submonoid R)
variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
variable {I : Ideal R} (δ : DividedPowers I)

private theorem exists_fraction {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ a : I, ∃ s : M, x = IsLocalization.mk' S (a : R) s := by
  obtain ⟨⟨a, s⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hx
  exact ⟨a, s, IsLocalization.eq_mk'_iff_mul_eq.mpr h⟩

/-- 局所化イデアルの外では分冪演算は零。 -/
theorem localizationDpow_null {n : ℕ} {x : S} (hx : x ∉ I.map (algebraMap R S)) :
    localizationDpow M S δ n x = 0 := by
  classical
  unfold localizationDpow
  rw [dite_eq_right hx]

/-- 局所化イデアル上の零次分冪は単位元。 -/
theorem localizationDpow_zero {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    localizationDpow M S δ 0 x = 1 := by
  obtain ⟨a, s, rfl⟩ := exists_fraction M S hx
  rw [localizationDpow_mk M S δ 0 a.property s, δ.dpow_zero a.property,
    pow_zero, IsLocalization.mk'_one, map_one]

/-- 局所化イデアル上の一次分冪は元自身。 -/
theorem localizationDpow_one {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    localizationDpow M S δ 1 x = x := by
  obtain ⟨a, s, rfl⟩ := exists_fraction M S hx
  rw [localizationDpow_mk M S δ 1 a.property s, δ.dpow_one a.property, pow_one]

/-- 正次数の分冪は局所化イデアルを保つ。 -/
theorem localizationDpow_mem {n : ℕ} {x : S} (hn : n ≠ 0)
    (hx : x ∈ I.map (algebraMap R S)) :
    localizationDpow M S δ n x ∈ I.map (algebraMap R S) := by
  obtain ⟨a, s, rfl⟩ := exists_fraction M S hx
  rw [localizationDpow_mk M S δ n a.property s]
  exact fraction_mem M S (δ.dpow_mem hn a.property) (s ^ n)

/-- 基底のイデアル上では、局所化写像と分冪演算は可換。 -/
theorem localizationDpow_algebraMap (n : ℕ) {a : R} (ha : a ∈ I) :
    localizationDpow M S δ n (algebraMap R S a) = algebraMap R S (δ.dpow n a) := by
  simpa only [one_pow, IsLocalization.mk'_one] using localizationDpow_mk M S δ n ha (1 : M)

/-- 局所化した分冪は次数に応じた斉次性を持つ。 -/
theorem localizationDpow_mul {n : ℕ} {a x : S} (hx : x ∈ I.map (algebraMap R S)) :
    localizationDpow M S δ n (a * x) = a ^ n * localizationDpow M S δ n x := by
  obtain ⟨c, s, rfl⟩ := exists_fraction M S hx
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective M a
  rw [← IsLocalization.mk'_mul,
    localizationDpow_mk M S δ n (I.mul_mem_left b c.property) (t * s),
    localizationDpow_mk M S δ n c.property s, δ.dpow_mul c.property,
    mul_pow, IsLocalization.mk'_mul, IsLocalization.mk'_pow]

/-- 同じ元の分冪の積は、元の環と同じ二項係数の公式を満たす。 -/
theorem localizationDpow_mul_dpow {m n : ℕ} {x : S}
    (hx : x ∈ I.map (algebraMap R S)) :
    localizationDpow M S δ m x * localizationDpow M S δ n x =
      (Nat.choose (m + n) m : S) * localizationDpow M S δ (m + n) x := by
  obtain ⟨a, s, rfl⟩ := exists_fraction M S hx
  rw [localizationDpow_mk M S δ m a.property s,
    localizationDpow_mk M S δ n a.property s,
    localizationDpow_mk M S δ (m + n) a.property s,
    ← IsLocalization.mk'_mul, ← pow_add, δ.mul_dpow a.property]
  calc
    _ = algebraMap R S (Nat.choose (m + n) m : R) *
        IsLocalization.mk' S (δ.dpow (m + n) a) (s ^ (m + n)) :=
      (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm
    _ = _ := by rw [map_natCast]

/-- 分冪の合成は、局所化後も同じ uniformBell の係数を持つ。 -/
theorem localizationDpow_comp {m n : ℕ} {x : S} (hn : n ≠ 0)
    (hx : x ∈ I.map (algebraMap R S)) :
    localizationDpow M S δ m (localizationDpow M S δ n x) =
      (Nat.uniformBell m n : S) * localizationDpow M S δ (m * n) x := by
  obtain ⟨a, s, rfl⟩ := exists_fraction M S hx
  rw [localizationDpow_mk M S δ n a.property s,
    localizationDpow_mk M S δ m (δ.dpow_mem hn a.property) (s ^ n),
    localizationDpow_mk M S δ (m * n) a.property s,
    δ.dpow_comp hn a.property, ← pow_mul, Nat.mul_comm n m]
  calc
    _ = algebraMap R S (Nat.uniformBell m n : R) *
        IsLocalization.mk' S (δ.dpow (m * n) a) (s ^ (m * n)) :=
      (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm
    _ = _ := by rw [map_natCast]

end SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
