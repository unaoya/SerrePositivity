module

public import SerrePositivity.CommutativeAlgebra.Witt.Lift
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.FieldTheory.Perfect
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.PerfectNilpotentLifting
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-! # 完全剰余体の完備局所環への Witt 係数写像

## 概要

剰余体 `k` が標数 `p` の完全体である完備 Noether 局所環 `D` には、剰余写像と両立する
`W(k) → D` がある（`exists_wittVector_residue_lift`）。`D` が標数零なら、この写像は単射かつ局所で
（`wittVector_ringHom_injective`、`wittVector_ringHom_isLocalHom`）、`W(k)` は `D` の Cohen 環になる
（`exists_wittVector_coefficient_embedding`）。

## 方針

`D` は `p` 進完備（`isAdicComplete_span_residue_characteristic`）なので、`D/p → k` の核について
`D/p` は完備。完全環からの持ち上げで `k → D/p` を作り、`Witt/Lift` の `wittResidueLift` で
`W(k) → D` へ延ばす。単射性は、`W(k)` が離散付値環で `p` が素元であることから、
`p` の冪と単元への分解（`ringHom_injective_of_dvr_uniformizer_powers`）で示す。

## 規約

係数写像は存在定理として述べる。途中の完全環からの持ち上げ（`PerfectNilpotentLifting`）が一意存在の
形でしか与えられていないため。Cohen の構造定理の混標数・完全剰余体の場合で、Mathlib への提出候補
（mathlib-upstream の G7）。

## 使われ方

混標数の Cohen 正規化（`Witt/Normalization`）。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity

section Embedding

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

end Embedding

section Construction

open IsLocalRing

/-- 完全剰余体を持つ完備Noether局所環には、剰余写像と両立するWitt係数写像が存在する。
標数零・整域性は写像の存在には不要。 -/
theorem exists_wittVector_residue_lift
    (D : Type*) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ f : WittVector p (ResidueField D) →+* D,
      (residue D).comp f = WittVector.constantCoeff := by
  let P : Ideal D := Ideal.span {(p : D)}
  have hP : P ≤ maximalIdeal D := by
    rw [Ideal.span_singleton_le_iff_mem, ← residue_eq_zero_iff]
    simp only [map_natCast, CharP.cast_eq_zero]
  let : Fact (¬ IsUnit (p : D)) := ⟨by
    simpa only [← mem_nonunits_iff, ← mem_maximalIdeal] using
      hP (Ideal.mem_span_singleton_self (p : D))⟩
  let : IsAdicComplete P D := isAdicComplete_span_residue_characteristic D p
  let q : ModP D p →+* ResidueField D :=
    Ideal.Quotient.lift P (residue D) (fun r hr ↦ (residue_eq_zero_iff r).mpr (hP hr))
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨r, rfl⟩ := residue_surjective (R := D) x
    exact ⟨Ideal.Quotient.mk P r, rfl⟩
  have hker : RingHom.ker q = (maximalIdeal D).map (Ideal.Quotient.mk P) := by
    exact (Ideal.ker_quotient_lift (residue D)
      (show P ≤ RingHom.ker (residue D) by rw [ker_residue]; exact hP)).trans
      (congrArg (fun J : Ideal D ↦ J.map (Ideal.Quotient.mk P)) ker_residue)
  let : IsAdicComplete (maximalIdeal D) (ModP D p) :=
    isAdicComplete_finite (R := D) (ModP D p)
  let : IsAdicComplete (RingHom.ker q) (ModP D p) := by
    rw [hker]
    exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal D) (ModP D p)).mpr
      inferInstance
  obtain ⟨s, hs, _⟩ := exists_unique_ringHom_lift_of_complete_kernel p q hq
    (RingHom.id (ResidueField D))
  refine ⟨wittResidueLift p D (ResidueField D) s, ?_⟩
  calc (residue D).comp (wittResidueLift p D (ResidueField D) s)
      = q.comp ((Ideal.Quotient.mk P).comp (wittResidueLift p D (ResidueField D) s)) := rfl
    _ = (q.comp s).comp WittVector.constantCoeff := by
      rw [wittResidueLift_mod_p]; rfl
    _ = WittVector.constantCoeff := by rw [hs]; rfl

/-- 標数零では、構成したWitt係数写像は剰余写像と両立する局所的な埋め込みとなる。
整域性は、この係数埋め込みの段階では不要。 -/
theorem exists_wittVector_coefficient_embedding
    (D : Type*) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [CharZero D]
    [IsAdicComplete (maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ f : WittVector p (ResidueField D) →+* D,
      Function.Injective f ∧ IsLocalHom f ∧
        (residue D).comp f = WittVector.constantCoeff := by
  obtain ⟨f, hf⟩ := exists_wittVector_residue_lift D p
  exact ⟨f, wittVector_ringHom_injective p f, wittVector_ringHom_isLocalHom p f, hf⟩

end Construction

end SerrePositivity
