module

public import SerrePositivity.BhattScholze.RankOneDPPrimeBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 既存一元分冪代数の実テンソル基底変更

通常代数の実比較射を既存mapとテンソル積の普遍性から構成する。
同型には両側のp局所性・p正則性を明示する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 基底係数の拡大と既存分冪代数のmapから得られる実テンソル比較射。 -/
def rankOneDPBaseChangeMap :
    B ⊗[A] DividedPowerAlgebra A A →ₐ[B] DividedPowerAlgebra B B :=
  Algebra.TensorProduct.lift (Algebra.ofId B (DividedPowerAlgebra B B))
    (DividedPowerAlgebra.map B (Algebra.linearMap A B)) (fun _ _ ↦ Commute.all _ _)

/-- 実比較射のすべての純テンソル上の式。 -/
theorem rankOneDPBaseChangeMap_tmul (b : B) (t : DividedPowerAlgebra A A) :
    rankOneDPBaseChangeMap (b ⊗ₜ[A] t) =
      algebraMap B (DividedPowerAlgebra B B) b *
        DividedPowerAlgebra.map B (Algebra.linearMap A B) t := rfl

/-- 標準分冪基底の純テンソルは拡大後の標準分冪基底へ写る。 -/
theorem rankOneDPBaseChangeMap_dp (n : ℕ) :
    rankOneDPBaseChangeMap ((1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp B n (1 : B) := by
  rw [rankOneDPBaseChangeMap_tmul, map_one, one_mul, DividedPowerAlgebra.map_apply_dp]
  simp only [Algebra.linearMap_apply, map_one]

variable {p : ℕ} [Fact p.Prime]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
variable (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
include hA hpA hB hpB

/-- p局所・p正則係数では、実テンソル比較射は全単射。 -/
theorem rankOneDPBaseChangeMap_bijective :
    Function.Bijective (rankOneDPBaseChangeMap (A := A) (B := B)) := by
  let bA := rankOneDPPrimeBasis hA hpA
  let bB := rankOneDPPrimeBasis hB hpB
  let bT := bA.baseChange B
  let e := bT.equiv bB (Equiv.refl ℕ)
  have he : (rankOneDPBaseChangeMap (A := A) (B := B)).toLinearMap = e.toLinearMap := by
    apply bT.ext
    intro n
    change rankOneDPBaseChangeMap (bT n) = e (bT n)
    rw [Module.Basis.equiv_apply]
    change rankOneDPBaseChangeMap ((bA.baseChange B) n) = bB n
    rw [Module.Basis.baseChange_apply]
    dsimp only [bA, bB]
    rw [rankOneDPPrimeBasis_apply, rankOneDPPrimeBasis_apply, rankOneDPBaseChangeMap_dp]
  change Function.Bijective (rankOneDPBaseChangeMap (A := A) (B := B)).toLinearMap
  rw [he]
  exact e.bijective

/-- p局所・p正則係数での、一元分冪代数の実基底変更同型。 -/
def rankOneDPBaseChangeEquiv :
    B ⊗[A] DividedPowerAlgebra A A ≃ₐ[B] DividedPowerAlgebra B B :=
  AlgEquiv.ofBijective rankOneDPBaseChangeMap
    (rankOneDPBaseChangeMap_bijective hA hpA hB hpB)

/-- 実基底変更同型も、全純テンソル上で構成した実比較射に一致する。 -/
theorem rankOneDPBaseChangeEquiv_tmul (b : B) (t : DividedPowerAlgebra A A) :
    rankOneDPBaseChangeEquiv hA hpA hB hpB (b ⊗ₜ[A] t) =
      algebraMap B (DividedPowerAlgebra B B) b *
        DividedPowerAlgebra.map B (Algebra.linearMap A B) t := rfl

end SerrePositivity.BhattScholze
