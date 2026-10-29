module

public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.FieldTheory.Perfect
public import SerrePositivity.CommutativeAlgebra.Adic.Complete

/-! # Witt係数の単射性と対象環のp進完備性

係数写像の存在とは独立に、与えられた写像の単射性を確認する。
Witt環から標数零の環への環写像は、pの冪と単元の分解から単射となる。
係数写像や剰余体との両立を新しい未証明入力として仮定する存在定理は置かない。
-/

public section
namespace SerrePositivity

/-- DVRからの環写像は、一様化元の全ての冪の像が非零なら単射。
終域の整域性・局所性・Noether性は不要。 -/
theorem ringHom_injective_of_dvr_uniformizer_powers
    {R D : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Ring D]
    (f : R →+* D) (π : R) (hπ : Irreducible π) (hpow : ∀ n : ℕ, f π ^ n ≠ 0) :
    Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  by_contra hx0
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have he : f x = 0 := hx
  rw [hu, map_mul, map_pow] at he
  exact hpow n (((u.isUnit.map f).mul_right_eq_zero).mp he)

/-- 完全な正標数体のWitt環から標数零の環への任意の環写像は単射。
終域の整域性・局所性・完備性は使わない。写像の存在は別の課題。 -/
theorem wittVector_ringHom_injective
    (p : ℕ) [hp : Fact p.Prime] {k D : Type*} [Field k] [CharP k p] [PerfectField k]
    [Ring D] [CharZero D] (f : WittVector p k →+* D) : Function.Injective f := by
  apply ringHom_injective_of_dvr_uniformizer_powers f (p : WittVector p k)
    (WittVector.irreducible p)
  intro n
  rw [map_natCast, ← Nat.cast_pow]
  exact Nat.cast_ne_zero.mpr (pow_ne_zero n hp.out.ne_zero)

/-- 任意のWitt係数写像は、源の極大イデアルを対象の(p)へ送る。 -/
theorem wittVector_map_maximalIdeal
    (p : ℕ) [Fact p.Prime] {k D : Type*} [Field k] [CharP k p] [PerfectField k]
    [CommRing D] (f : WittVector p k →+* D) :
    (IsLocalRing.maximalIdeal (WittVector p k)).map f = Ideal.span {(p : D)} := by
  rw [(WittVector.irreducible p).maximalIdeal_eq, Ideal.map_span]
  simp only [Set.image_singleton, map_natCast]

/-- 剰余標数pの局所環へのWitt係数写像は局所準同型。
対象のNoether性・完備性・標数零・整域性は不要。 -/
theorem wittVector_ringHom_isLocalHom
    (p : ℕ) [Fact p.Prime] {k D : Type*} [Field k] [CharP k p] [PerfectField k]
    [CommRing D] [IsLocalRing D] [CharP (IsLocalRing.ResidueField D) p]
    (f : WittVector p k →+* D) : IsLocalHom f := by
  apply ((IsLocalRing.local_hom_TFAE f).out 1 3).mpr
  rw [wittVector_map_maximalIdeal p f, Ideal.span_singleton_le_iff_mem,
    ← IsLocalRing.residue_eq_zero_iff]
  simp only [map_natCast, CharP.cast_eq_zero]

/-- 剰余標数pの完備Noether局所環はp進完備。
対象環の整域性・標数零・剰余体の完全性はこの完備性の供給には不要。 -/
theorem isAdicComplete_span_residue_characteristic
    (D : Type*) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (p : ℕ) [CharP (IsLocalRing.ResidueField D) p] :
    IsAdicComplete (Ideal.span {(p : D)}) D := by
  apply isAdicComplete_finite_of_le_maximalIdeal
  rw [Ideal.span_singleton_le_iff_mem, ← IsLocalRing.residue_eq_zero_iff]
  simp only [map_natCast, CharP.cast_eq_zero]

end SerrePositivity
