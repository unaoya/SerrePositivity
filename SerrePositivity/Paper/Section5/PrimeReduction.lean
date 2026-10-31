module

public import SerrePositivity.Paper.Section5.Core
public import SerrePositivity.CommutativeAlgebra.SupportDimension
public import SerrePositivity.IntersectionMultiplicity.Basic

/-! # 核心定理の零次元境界

零次元の素イデアル商は剰余体であり、次元の和が環の次元に一致するなら相手は環自身である。
この場合の交点重複度を `1` と計算し、核心定理から正次元という制約を外す。
-/

public section

universe u

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

variable {R : Type u} [CommRing R]

/-- 局所環の零次元の素イデアル商は剰余体である。 -/
theorem prime_eq_maximalIdeal_of_quotient_dim_zero [IsLocalRing R]
    (P : Ideal R) [P.IsPrime] (hP : ringKrullDim (R ⧸ P) = 0) :
    P = maximalIdeal R := by
  refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime))) ?_
  have hp : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Module.support R (R ⧸ P) :=
    Module.mem_support_iff_of_finite.mpr (by rw [Ideal.annihilator_quotient])
  rw [support_of_supportDim_eq_zero R (R ⧸ P) (by
    rwa [Module.supportDim_quotient_eq_ringKrullDim])] at hp
  exact hp

/-- 環自身と剰余体の交点重複度は `1`。 -/
theorem chi_self_residueField [IsLocalRing R] : chi R R (ResidueField R) = 1 := by
  let : IsSimpleModule R (ResidueField R) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))
  have h := chi_of_finite_free_left (R := R) R (ResidueField R)
  have h' : (chi R R (ResidueField R) : ℝ) = 1 := by simpa using h
  exact_mod_cast h'

/-- 一方が零次元の素イデアル商である固有交叉では、交点重複度は `1`。 -/
theorem chi_prime_eq_one_of_dim_zero [IsRegularLocalRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : ringKrullDim (R ⧸ P) = 0)
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R) :
    chi R (R ⧸ P) (R ⧸ Q) = 1 := by
  let : IsDomain R := isDomain_of_isRegularLocalRing R
  have hQ := ideal_eq_bot_of_quotient_dim_eq Q (by simpa [hP] using hsum)
  have hp := prime_eq_maximalIdeal_of_quotient_dim_zero P hP
  subst P
  subst Q
  rw [chi_congr (LinearEquiv.refl R _) (AlgEquiv.quotientBot R R).toLinearEquiv,
    chi_comm]
  exact chi_self_residueField

/-- 完備・代数閉剰余体の場合、次元零の境界も含めた素イデアル商の正値性。 -/
theorem chi_prime_pos_of_complete_algClosed
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hfin : Module.length R ((R ⧸ P) ⊗[R] (R ⧸ Q)) ≠ ⊤)
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  by_cases hp : ringKrullDim (R ⧸ P) = 0
  · rw [chi_prime_eq_one_of_dim_zero P Q hp hsum]
    norm_num
  by_cases hq : ringKrullDim (R ⧸ Q) = 0
  · rw [chi_comm, chi_prime_eq_one_of_dim_zero Q P hq (by simpa [add_comm] using hsum)]
    norm_num
  exact core_of_complete_algClosed R p P Q
    (lt_of_le_of_ne (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ P)) (Ne.symm hp))
    (lt_of_le_of_ne (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Q)) (Ne.symm hq)) hsum
    (radical_sup_eq_maximalIdeal_of_tensor_finiteLength P Q hfin)

end SerrePositivity.Section5
