module

public import SerrePositivity.Paper.Section5.Setup
public import SerrePositivity.CommutativeAlgebra.SupportDimension
public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.IntersectionMultiplicity.Additivity
public import SerrePositivity.Paper.Section2.ResidueFieldExtension
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import SerrePositivity.IntersectionMultiplicity.EqualCharZero.Positivity

/-! # 核の場合への帰着（論文 Lemma 5.1）

## 概要

正則局所環の有限生成加群の交点重複度の正値性を、完備・剰余体が代数閉・素イデアル商の核の場合に帰着する。完備化（Noether 性と平坦局所拡大の保存則）、Lemma 2.1 による剰余体の拡大、両変数のデヴィサージュ、零次元の境界（相手が環自身で重複度 `1`）を順に適用する。剰余標数零の場合は Serre の対角線論法（IntersectionMultiplicity/EqualCharZeroPositivity）で示す。

## 規約

デヴィサージュは交点重複度の消滅定理の引用に依存する。

## 使われ方

Paper/Statement。
-/

public section

universe u

section PrimeReductionPart

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

end PrimeReductionPart

section ModuleReductionPart

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 剰余標数が正の完備正則局所環で剰余体が代数閉なら、任意の有限生成加群について正値性が成り立つ。
素イデアル商へのデヴィサージュを内部で行い、正次元の仮定は要求しない。
核の場合と同じ引用入力、および既存の交点消滅定理に依存する。 -/
theorem positivity_of_complete_algClosed
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N :=
  chi_pos_of_prime_quotients (chi_prime_pos_of_complete_algClosed R p) M N hfin hdim

end SerrePositivity.Section5

end ModuleReductionPart

section ResidueFieldReductionPart

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 完備正則局所環で剰余標数が正なら、任意の有限生成加群に対して正値性が成り立つ。
剰余体は代数閉でなくてよい。Lemma 2.1 と核心定理の既存の引用入力に依存する。 -/
theorem positivity_of_complete_residueCharP
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  obtain ⟨S, sRing, sLocal, sNoetherian, sComplete, rsAlg, rsLocal,
      hflat, hm, ⟨ek, _⟩, _, hregular, _⟩ := Section2.lemma_2_1 R
  let := hflat
  let : IsRegularLocalRing S := hregular inferInstance
  let : IsAlgClosed (ResidueField S) := IsAlgClosed.of_ringEquiv _ _ ek.symm
  let : CharP (ResidueField S) p := charP_of_injective_ringHom
    (f := ResidueField.map (algebraMap R S)) (RingHom.injective _) p
  rw [← chi_baseChange_of_map_maximalIdeal R S hm M N]
  apply positivity_of_complete_algClosed S p (S ⊗[R] M) (S ⊗[R] N)
  · rwa [tensorLength_baseChange_of_map_maximalIdeal R S hm M N]
  · rwa [supportDim_baseChange_of_map_maximalIdeal R S hm M,
      supportDim_baseChange_of_map_maximalIdeal R S hm N,
      ringKrullDim_eq_of_flat_of_map_maximalIdeal R S hm]

end SerrePositivity.Section5

end ResidueFieldReductionPart

section CompletionReductionPart

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 正の剰余標数の正則局所環で正値性が成り立つ。
完備化で有限長・次元・正則性・χを保存し、完備な場合に帰着する。
新しい未証明入力はなく、核心定理などの既存の引用入力に依存する。 -/
theorem positivity_of_residueCharP
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  let S := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing S := isNoetherianRing_adicCompletion R (maximalIdeal R)
  have hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    AdicCompletion.maximalIdeal_eq_map.symm
  let : IsRegularLocalRing S := isRegularLocalRing_of_flat_of_map_maximalIdeal R S hm
  let : CharP (ResidueField S) p := charP_of_injective_ringHom
    (f := ResidueField.map (algebraMap R S)) (RingHom.injective _) p
  rw [← chi_baseChange_of_map_maximalIdeal R S hm M N]
  apply positivity_of_complete_residueCharP S p (S ⊗[R] M) (S ⊗[R] N)
  · rwa [tensorLength_baseChange_of_map_maximalIdeal R S hm M N]
  · rwa [supportDim_baseChange_of_map_maximalIdeal R S hm M,
      supportDim_baseChange_of_map_maximalIdeal R S hm N,
      ringKrullDim_eq_of_flat_of_map_maximalIdeal R S hm]

end SerrePositivity.Section5

end CompletionReductionPart

section CharacteristicZeroReductionPart

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 剰余標数零の場合の正値性。対角線論法による証明済みの定理を適用する。 -/
theorem positivity_of_residueCharZero
    (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N :=
  chi_pos_of_residueCharZero R M N hfin hdim

end SerrePositivity.Section5

end CharacteristicZeroReductionPart
