module

public import SerrePositivity.CommutativeAlgebra.RegularSequence

/-! # 主極大イデアルを持つ局所環での非零元の分解

極大イデアルがxで生成されるとき、xで割れない元は単元。
Noether性とKrullの共通部分定理による有限位数の補題を合わせて、
非零元をxの冪と単元の積に分ける。離散付値の理論全体は必要ない。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- 極大イデアルの生成元で割れない元は単元。 -/
theorem isUnit_of_not_dvd_of_principal_maximalIdeal (x a : R)
    (hx : Ideal.span {x} = maximalIdeal R) (ha : ¬ x ∣ a) : IsUnit a := by
  by_contra hunit
  apply ha
  apply Ideal.mem_span_singleton.mp
  rw [hx]
  exact (mem_maximalIdeal a).mpr hunit

/-- Noether局所環の主極大イデアルの生成元は、全ての非零元の有限位数を与える。 -/
theorem exists_pow_mul_unit_of_principal_maximalIdeal [IsNoetherianRing R]
    (x a : R) (hx : Ideal.span {x} = maximalIdeal R) (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ b : R, a = x ^ n * b ∧ IsUnit b := by
  have hxm : x ∈ maximalIdeal R := hx ▸ Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨n, b, hab, hb⟩ := exists_pow_mul_not_dvd x a hxm ha
  exact ⟨n, b, hab, isUnit_of_not_dvd_of_principal_maximalIdeal x b hx hb⟩

/-- 一元の極大イデアル生成族で、その一元は主極大イデアルを生成する。 -/
theorem span_parameter_fin_one (t : Fin 1 → R)
    (ht : Ideal.span (Set.range t) = maximalIdeal R) :
    Ideal.span {t 0} = maximalIdeal R := by
  have hr : Set.range t = {t 0} := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg t (Subsingleton.elim i 0))
    · rintro rfl
      exact Set.mem_range_self 0
  rwa [hr] at ht

end SerrePositivity
