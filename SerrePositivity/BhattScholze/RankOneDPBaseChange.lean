module

public import SerrePositivity.BhattScholze.RankOneDPPrimeBasis
public import SerrePositivity.BhattScholze.RankOneDPBaseChangeUniversal

/-! # 既存一元分冪代数の実テンソル基底変更

任意係数の実比較同型から、従来のp局所・p正則な公開署名を保つ互換入口を得る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

variable {p : ℕ} [Fact p.Prime]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
variable (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
include hA hpA hB hpB

set_option linter.unusedSectionVars false in
/-- p局所・p正則係数では、実テンソル比較射は全単射。 -/
theorem rankOneDPBaseChangeMap_bijective :
    Function.Bijective (rankOneDPBaseChangeMap (A := A) (B := B)) :=
  (rankOneDPBaseChangeUniversalEquiv (A := A) (B := B)).bijective

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
