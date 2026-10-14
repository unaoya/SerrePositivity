module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # 係数制限の核の普遍微分による表示

Mathlibの通常の推移列を使い、核を底環の元の微分が張る部分加群へ同定する。
有限性・Noether性・標数は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable (R A S : Type*) [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
open scoped TensorProduct

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

end SerrePositivity
