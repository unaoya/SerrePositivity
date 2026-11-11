module

public import SerrePositivity.AlgebraicGeometry.FractionFieldCommonDenominator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
概要：同じ分数体を持つ有限型アフィン環には、基底上で同型な非空の主開がある。
方針：双方の生成元の分母を払い、双方の分母を同時に反転した部分代数を比較する。
規約：分数体への二つの写像は、共通の基底環上で両立するとする。
使われ方：滑らかなアフィン環を関数体が同じ超曲面模型と比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped nonZeroDivisors

private theorem ofField_restrictScalars_le
    {A B K : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    {b : B} (hb : b ≠ 0) {V : Subalgebra A K}
    (hBase : (IsScalarTower.toAlgHom A B K).range ≤ V)
    (hInv : (algebraMap B K b)⁻¹ ∈ V) :
    (Localization.subalgebra.ofField K (Submonoid.powers b)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hb)).restrictScalars A ≤ V := by
  intro x hx
  change ∃ (a t : B) (_ : t ∈ Submonoid.powers b),
    x = algebraMap B K a * (algebraMap B K t)⁻¹ at hx
  obtain ⟨a, _, ⟨n, rfl⟩, rfl⟩ := hx
  rw [map_pow, ← inv_pow]
  exact V.mul_mem (hBase ⟨a, rfl⟩) (V.pow_mem hInv _)

private theorem exists_away_inverting_fraction
    {A B K : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    {b : B} (hb : b ≠ 0) {x : K} (hx : x ≠ 0)
    (hxU : x ∈ Localization.subalgebra.ofField K (Submonoid.powers b)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hb)) :
    ∃ (c : B) (hc : c ≠ 0) (n : ℕ),
      algebraMap B K c = algebraMap B K b ^ n * x ∧
      (algebraMap B K b)⁻¹ ∈ Localization.subalgebra.ofField K (Submonoid.powers c)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hc) ∧
      x⁻¹ ∈ Localization.subalgebra.ofField K (Submonoid.powers c)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hc) := by
  change ∃ (a t : B) (_ : t ∈ Submonoid.powers b),
    x = algebraMap B K a * (algebraMap B K t)⁻¹ at hxU
  obtain ⟨a, _, ⟨n, rfl⟩, hxa⟩ := hxU
  have ha : a ≠ 0 := fun h => hx (by simp [hxa, h])
  have hbK : algebraMap B K b ≠ 0 :=
    fun h => hb ((IsFractionRing.injective B K) (h.trans (map_zero _).symm))
  have haK : algebraMap B K a ≠ 0 :=
    fun h => ha ((IsFractionRing.injective B K) (h.trans (map_zero _).symm))
  have he : algebraMap B K (b * a) = algebraMap B K b ^ (n + 1) * x := by
    rw [hxa, map_mul, map_pow, pow_succ]
    field_simp
  refine ⟨b * a, mul_ne_zero hb ha, n + 1, he, ?_, ?_⟩
  · change ∃ (d t : B) (_ : t ∈ Submonoid.powers (b * a)),
      (algebraMap B K b)⁻¹ = algebraMap B K d * (algebraMap B K t)⁻¹
    refine ⟨a, b * a, Submonoid.mem_powers _, ?_⟩
    rw [map_mul]
    field_simp
  · change ∃ (d t : B) (_ : t ∈ Submonoid.powers (b * a)),
      x⁻¹ = algebraMap B K d * (algebraMap B K t)⁻¹
    refine ⟨b ^ (n + 1), b * a, Submonoid.mem_powers _, ?_⟩
    rw [he, map_pow]
    field_simp

/--
概要：同じ分数体を持つ二つの有限型整域には、基底上で同型な非零元による局所化がある。
方針：各代数を他方の局所化に入れ、両方の分母を反転した部分代数を同定する。
規約：分数体への代数構造は共通の基底環上で両立する。
使われ方：超曲面と双有理なアフィン環に共通の主開を選ぶ。
-/
theorem exists_away_algEquiv_of_common_fractionField
    {A B C K : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing C] [IsDomain C]
    [Algebra A B] [Algebra A C] [Algebra.FiniteType A B] [Algebra.FiniteType A C]
    [Field K] [Algebra A K] [Algebra B K] [Algebra C K]
    [IsFractionRing B K] [IsFractionRing C K] [IsScalarTower A B K] [IsScalarTower A C K] :
    ∃ (b : B) (_ : b ≠ 0) (c : C) (_ : c ≠ 0),
      Nonempty (Localization.Away b ≃ₐ[A] Localization.Away c) := by
  let f := IsScalarTower.toAlgHom A B K
  let g := IsScalarTower.toAlgHom A C K
  let : Algebra.FiniteType A f.range := .of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : Algebra.FiniteType A g.range := .of_surjective g.rangeRestrict g.rangeRestrict_surjective
  obtain ⟨b, hb, hB⟩ := exists_nonzero_le_fractionField_away_of_finiteType (B := B) g.range
  obtain ⟨c, hc, hC⟩ := exists_nonzero_le_fractionField_away_of_finiteType (B := C) f.range
  have hbK : f b ≠ 0 := fun h => hb ((IsFractionRing.injective B K) (h.trans (map_zero f).symm))
  have hcK : g c ≠ 0 := fun h => hc ((IsFractionRing.injective C K) (h.trans (map_zero g).symm))
  obtain ⟨b', hb', n, hbEq, hbInvB, hcInvB⟩ :=
    exists_away_inverting_fraction (A := A) hb hcK (hB (show g c ∈ g.range from ⟨c, rfl⟩))
  obtain ⟨c', hc', m, hcEq, hcInvC, hbInvC⟩ :=
    exists_away_inverting_fraction (A := A) hc hbK (hC (show f b ∈ f.range from ⟨b, rfl⟩))
  let U := Localization.subalgebra.ofField K (Submonoid.powers b')
    (powers_le_nonZeroDivisors_of_noZeroDivisors hb')
  let V := Localization.subalgebra.ofField K (Submonoid.powers c')
    (powers_le_nonZeroDivisors_of_noZeroDivisors hc')
  have hBaseU : f.range ≤ U.restrictScalars A := by
    rintro _ ⟨x, rfl⟩
    exact U.algebraMap_mem x
  have hBaseV : g.range ≤ V.restrictScalars A := by
    rintro _ ⟨x, rfl⟩
    exact V.algebraMap_mem x
  have hBU : g.range ≤ U.restrictScalars A :=
    hB.trans (ofField_restrictScalars_le hb hBaseU hbInvB)
  have hCV : f.range ≤ V.restrictScalars A :=
    hC.trans (ofField_restrictScalars_le hc hBaseV hcInvC)
  have hUV : U.restrictScalars A = V.restrictScalars A := by
    apply le_antisymm
    · refine ofField_restrictScalars_le hb' hCV ?_
      rw [hbEq, mul_inv_rev, ← inv_pow]
      exact V.mul_mem hcInvC (V.pow_mem hbInvC n)
    · refine ofField_restrictScalars_le hc' hBU ?_
      rw [hcEq, mul_inv_rev, ← inv_pow]
      exact U.mul_mem hbInvB (U.pow_mem hcInvB m)
  let eB := IsLocalization.algEquiv (Submonoid.powers b') (Localization.Away b') U
  let eC := IsLocalization.algEquiv (Submonoid.powers c') (Localization.Away c') V
  exact ⟨b', hb', c', hc',
    ⟨(eB.restrictScalars A).trans
      ((Subalgebra.equivOfEq _ _ hUV).trans (eC.restrictScalars A).symm)⟩⟩

end SerrePositivity.AlgebraicGeometry
