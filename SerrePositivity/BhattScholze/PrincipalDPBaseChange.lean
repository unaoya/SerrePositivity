module

public import SerrePositivity.BhattScholze.RankOneDPBaseChange
public import SerrePositivity.BhattScholze.PrincipalDPBaseChangeUniversal

/-! # 一元分冪表示環の実テンソル基底変更

通常の商環とテンソルの同型を既存APIから構成する。導来比較は含まない。
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

/-- 実テンソル同型による表示関係イデアルの像は、標的の表示関係イデアル。 -/
theorem principalDPBaseChange_relationIdeal (y : A) :
    principalDPRelationIdeal (algebraMap A B y) =
      ((principalDPRelationIdeal y).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom).map
          (rankOneDPBaseChangeEquiv hA hpA hB hpB).toRingHom :=
  principalDPBaseChangeUniversal_relationIdeal (B := B) y

/-- 一元分冪表示環は、p局所・p正則な係数環の基底変更と可換。 -/
def principalDPBaseChangeEquiv (y : A) :
    B ⊗[A] PrincipalDPPresentation A y ≃ₐ[B]
      PrincipalDPPresentation B (algebraMap A B y) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B (DividedPowerAlgebra A A) B
    (principalDPRelationIdeal y)).trans
    (Ideal.quotientEquivAlg _ _ (rankOneDPBaseChangeEquiv hA hpA hB hpB)
      (principalDPBaseChange_relationIdeal hA hpA hB hpB y))

/-- 実商の基底変更同型はBの係数を保つ。 -/
theorem principalDPBaseChangeEquiv_coeff (y : A) (b : B) :
    principalDPBaseChangeEquiv hA hpA hB hpB y
      (b ⊗ₜ[A] (1 : PrincipalDPPresentation A y)) =
      algebraMap B (PrincipalDPPresentation B (algebraMap A B y)) b :=
  (principalDPBaseChangeEquiv hA hpA hB hpB y).commutes b

/-- 実商の基底変更同型の、標準生成元の全純テンソル上の式。 -/
theorem principalDPBaseChangeEquiv_tmul_generator (y : A) (b : B) (n : ℕ) :
    principalDPBaseChangeEquiv hA hpA hB hpB y (b ⊗ₜ[A] principalDPGenerator y n) =
      algebraMap B (PrincipalDPPresentation B (algebraMap A B y)) b *
        principalDPGenerator (algebraMap A B y) n :=
  principalDPBaseChangeUniversalEquiv_tmul_generator y b n

end SerrePositivity.BhattScholze
