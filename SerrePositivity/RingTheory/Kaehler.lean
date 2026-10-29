module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Unramified.Field
public import SerrePositivity.RingTheory.Derivation

/-! # Kähler 微分の一般論

概要：通常の Kähler 微分 `Ω_{S/R}` についての一般的な事実。
- 代数の生成元の微分が `Ω_{S/R}` を張る。
- 底の拡大 `R → A` に沿う係数制限 `Ω_{S/R} → Ω_{S/A}` の核は `D(A)` が張る部分加群。
- `A/R` が形式不分岐なら係数制限は同型。
- 有限体拡大は、相対微分が零（次元 0）であることと分離的であることが同値。
方針：生成は導分の一般論（`span_range_derivation_eq_span_of_adjoin_eq_top`）を普遍導分に適用する。
核と同型は Mathlib の第一基本完全列（`KaehlerDifferential.exact_mapBaseChange_map`・`range_mapBaseChange`）、
分離性は Mathlib の `Algebra.FormallyUnramified.iff_isSeparable` と `formallyUnramified_iff` から。
規約：有限性・Noether 性・標数は、分離性の判定以外では仮定しない。
使われ方：p 基底と一元添加の微分（FieldTheory）、中間係数体上の微分、分数体での分離性の判定。
Mathlib への提出候補（mathlib-upstream）。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct

section Span

/-- 通常の Kähler 微分は代数の生成元の微分で生成される。 -/
theorem span_kaehlerDifferential_of_adjoin_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (hs : Algebra.adjoin R s = ⊤) :
    Submodule.span S (KaehlerDifferential.D R S '' s) = ⊤ := by
  rw [← span_range_derivation_eq_span_of_adjoin_eq_top (KaehlerDifferential.D R S) s hs]
  exact KaehlerDifferential.span_range_derivation R S


end Span

section RestrictionKernel

variable (R A S : Type*) [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]

/-- 底環を拡大した係数制限の核は、追加した定数の微分で生成される。 -/
theorem ker_kaehlerRestriction_eq_span :
    LinearMap.ker (KaehlerDifferential.map R A S S) =
      Submodule.span S (Set.range (fun a : A ↦
        KaehlerDifferential.D R S (algebraMap A S a))) := by
  rw [← KaehlerDifferential.range_mapBaseChange]
  let P := Submodule.span S (Set.range (fun a : A ↦
    KaehlerDifferential.D R S (algebraMap A S a)))
  have hω (ω : KaehlerDifferential R A) : KaehlerDifferential.map R R A S ω ∈ P := by
    have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero => simp [P]
    | add x y _ _ hx hy => simpa using P.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact P.smul_of_tower_mem a hx
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x with
    | tmul s ω =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      exact P.smul_mem s (hω ω)
    | add x y hx hy => simpa using P.add_mem hx hy
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    refine ⟨1 ⊗ₜ[A] KaehlerDifferential.D R A a, ?_⟩
    simp

end RestrictionKernel

section Coefficients
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyUnramified R S]

/-- 底環の微分が零なら、係数をその底環拡大へ移しても相対微分は変わらない。 -/
def relativeDifferentialEquivOfFormallyUnramified :
    KaehlerDifferential R T ≃ₗ[T] KaehlerDifferential S T := by
  apply LinearEquiv.ofBijective (KaehlerDifferential.map R S T T)
  refine ⟨?_, KaehlerDifferential.map_surjective R S T⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

@[simp] theorem relativeDifferentialEquivOfFormallyUnramified_D (t : T) :
    relativeDifferentialEquivOfFormallyUnramified R S T (KaehlerDifferential.D R T t) =
      KaehlerDifferential.D S T t := by
  exact KaehlerDifferential.map_D R S T T t
end Coefficients

section Fields
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]

/-- 有限体拡大では、通常の相対微分が零であることと分離性が同値。 -/
theorem isSeparable_iff_subsingleton_kaehlerDifferential :
    Algebra.IsSeparable K L ↔ Subsingleton (KaehlerDifferential K L) := by
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  exact Algebra.formallyUnramified_iff K L

/-- 微分の有限性を確認した有限体拡大の次元0による分離性判定。 -/
theorem isSeparable_iff_finrank_kaehlerDifferential_eq_zero :
    Algebra.IsSeparable K L ↔ Module.finrank L (KaehlerDifferential K L) = 0 := by
  rw [Module.finrank_zero_iff, isSeparable_iff_subsingleton_kaehlerDifferential]
end Fields

end SerrePositivity
