module

public import SerrePositivity.BhattScholze.PerfectCoefficientTensor
public import SerrePositivity.BhattScholze.CompatibleRootFamilyIdeal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # B4-6：全射商の通常底変換の核

全射algebraMap R Sの核をTへ拡張したイデアルが、T→S⊗[R]Tの実際の核である。
平坦性・完備性・有限生成性は要求しない。根付き生成族の入力の接続に使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- 全射商を通常底変換した標準射の核は、元の核の拡張イデアル。 -/
theorem tensorBaseChangeKernel_eq_map (hq : Function.Surjective (algebraMap R S)) :
    RingHom.ker (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R T) := by
  let J := RingHom.ker (algebraMap R S)
  let I := J.map (algebraMap R T)
  let U := T ⧸ I
  let qU := Ideal.Quotient.mk I
  have hle : J ≤ RingHom.ker (qU.comp (algebraMap R T)) := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  let g := (algebraMap R S).liftOfSurjective hq ⟨qU.comp (algebraMap R T), hle⟩
  have hg (r : R) : g (algebraMap R S r) = qU (algebraMap R T r) :=
    RingHom.liftOfSurjective_comp_apply _ _ _ r
  let L := coefficientTensorLift g qU hg
  let iT := (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  apply le_antisymm
  · intro t ht
    have hL : L (iT t) = qU t := by
      change coefficientTensorLift g qU hg ((1 : S) ⊗ₜ[R] t) = qU t
      rw [coefficientTensorLift_tmul, map_one, one_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change iT t = 0 at ht
    rw [← hL, ht, map_zero]
  · change J.map (algebraMap R T) ≤ RingHom.ker iT
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change iT (algebraMap R T r) = 0
    change algebraMap R S r = 0 at hr
    calc
      iT (algebraMap R T r) =
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) (algebraMap R S r) :=
        ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes r).trans
          ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes r).symm
      _ = 0 := by rw [hr, map_zero]

/-- 元の核の生成族の像を初項とする族は、通常底変換の核を初項イデアルとして生成する。
この核の同定自体には、後続項が根であることは必要ない。 -/
theorem tensorBaseChangeKernel_eq_rootFamilyZeroIdeal
    (hq : Function.Surjective (algebraMap R S))
    {σ : Type u} (a : σ → R) (ha : RingHom.ker (algebraMap R S) = Ideal.span (Set.range a))
    (ρ : σ → ℕ → T) (hρ0 : ∀ s, ρ s 0 = algebraMap R T (a s)) :
    RingHom.ker (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom =
      compatibleRootFamilyZeroIdeal ρ := by
  rw [tensorBaseChangeKernel_eq_map hq, ha, Ideal.map_span, ← Set.range_comp]
  unfold compatibleRootFamilyZeroIdeal
  congr 1
  exact congrArg Set.range (funext hρ0).symm

end SerrePositivity.BhattScholze
