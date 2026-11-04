module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericVanishing

/-!
# 一般点での p 冪 torsion の延長

## 概要
有限加群が一般点で p 冪 torsion なら、一つの分母と p を反転すると消える。

## 方針
有限個の生成元の p 冪関係について、基底の分母をまとめて払う。

## 規約
p は任意の基底環の元。この補題では素数性を必要としない。

## 使われ方
一般点で p 反転後に同型となる射の核と余核に適用する。
-/

@[expose] public section
noncomputable section
universe u v

namespace SerrePositivity.CommutativeAlgebra

/-- 一般点での p 冪 torsion は、基底の一つの分母と p の反転で消える。 -/
theorem exists_away_mul_subsingleton_of_localized_power_torsion
    {R : Type u} [CommRing R] (S : Submonoid R) (p : R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ x : M, ∃ n : ℕ,
      p ^ n • LocalizedModule.mkLinearMap S M x = 0) :
    ∃ g : S, Subsingleton (LocalizedModule.Away ((g : R) * p) M) := by
  classical
  obtain ⟨k, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose n hn using fun i ↦ h (v i)
  have hker (i : Fin k) : p ^ n i • v i ∈
      LinearMap.ker (LocalizedModule.mkLinearMap S M) := by
    simpa only [LinearMap.mem_ker, map_smul] using hn i
  choose r hrS hr using fun i ↦ LocalizedModule.mem_ker_mkLinearMap_iff.mp (hker i)
  let g : S := ⟨∏ i, r i, S.prod_mem fun i _ ↦ hrS i⟩
  refine ⟨g, LocalizedModule.subsingleton_iff_ker_eq_top.mpr ?_⟩
  apply top_unique
  rw [← hv]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply LocalizedModule.mem_ker_mkLinearMap_iff.mpr
  refine ⟨((g : R) * p) ^ (n i + 1), ⟨n i + 1, rfl⟩, ?_⟩
  have hd : r i * p ^ n i ∣ ((g : R) * p) ^ (n i + 1) := by
    rw [mul_pow]
    exact mul_dvd_mul
      ((Finset.dvd_prod_of_mem r (Finset.mem_univ i)).trans
        (dvd_pow_self (g : R) (Nat.succ_ne_zero _)))
      (pow_dvd_pow p (Nat.le_succ _))
  obtain ⟨a, ha⟩ := hd
  rw [ha, mul_smul, smul_comm, mul_smul, hr i, smul_zero]

end SerrePositivity.CommutativeAlgebra
