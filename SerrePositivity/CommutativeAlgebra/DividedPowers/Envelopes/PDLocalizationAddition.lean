module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDLocalizationLaws

/-!
# 局所化した分冪の加法公式

## 概要
分数表示の分冪は、元の分冪と同じ反対角線の加法公式を満たす。

## 方針
二つの分母の積に通分し、各反対角線項の分母を払って元の環で比較する。

## 規約
正則な分母を仮定せず、局所化の分数の等式判定を使う。

## 使われ方
Berthelot I.1.7.1、III.4。結晶厚化の主開局所化の分冪構造。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
variable {R : Type u} [CommRing R] (M : Submonoid R)
variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
variable {I : Ideal R} (δ : DividedPowers I)

private theorem mk'_sum {ι : Type v} (A : Finset ι) (f : ι → R) (s : M) :
    IsLocalization.mk' S (A.sum f) s = A.sum (fun i => IsLocalization.mk' S (f i) s) := by
  rw [IsLocalization.mk'_eq_mul_mk'_one, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact (IsLocalization.mk'_eq_mul_mk'_one (f i) s).symm

private theorem add_term (i j : ℕ) (a b : R) (s t : M) :
    IsLocalization.mk' S
      (((t : R) ^ i * δ.dpow i a) * ((s : R) ^ j * δ.dpow j b)) ((s * t) ^ (i + j)) =
        IsLocalization.mk' S (δ.dpow i a) (s ^ i) *
          IsLocalization.mk' S (δ.dpow j b) (t ^ j) := by
  rw [← IsLocalization.mk'_mul]
  apply IsLocalization.mk'_eq_of_eq
  simp only [SubmonoidClass.coe_pow, Submonoid.coe_mul, mul_pow, pow_add]
  ring

/-- 局所化した分冪は加法の反対角線の公式を満たす。 -/
theorem localizationDpow_add {n : ℕ} {x y : S}
    (hx : x ∈ I.map (algebraMap R S)) (hy : y ∈ I.map (algebraMap R S)) :
    localizationDpow M S δ n (x + y) =
      (Finset.antidiagonal n).sum (fun k =>
        localizationDpow M S δ k.1 x * localizationDpow M S δ k.2 y) := by
  obtain ⟨⟨a, s⟩, ha⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hx
  obtain ⟨⟨b, t⟩, hb⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hy
  have hxa : x = IsLocalization.mk' S (a : R) s := IsLocalization.eq_mk'_iff_mul_eq.mpr ha
  have hyb : y = IsLocalization.mk' S (b : R) t := IsLocalization.eq_mk'_iff_mul_eq.mpr hb
  rw [hxa, hyb, ← IsLocalization.mk'_add, mul_comm (a : R) (t : R), mul_comm (b : R) (s : R)]
  rw [localizationDpow_mk M S δ n
      (I.add_mem (I.mul_mem_left (t : R) a.property) (I.mul_mem_left (s : R) b.property))
      (s * t), δ.dpow_add (I.mul_mem_left (t : R) a.property) (I.mul_mem_left (s : R) b.property),
    mk'_sum M S]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [localizationDpow_mk M S δ ij.1 a.property s,
    localizationDpow_mk M S δ ij.2 b.property t,
    δ.dpow_mul a.property, δ.dpow_mul b.property, ← hsum]
  exact add_term M S δ ij.1 ij.2 a b s t

end SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
