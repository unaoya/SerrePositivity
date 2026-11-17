module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeBaseChangeCoefficients

/-!
# 元のfull envelopeの完備テンソル比較の純テンソル

## 概要
元の比較に選ばれた環同型は、元の純テンソルを元の係数射の線形延長へ送る。

## 方針
元の左右の係数脚の等式と純テンソルの積表示を使う。

## 規約
既存のexists_affineEnvelopeCoefficientBaseChange_equivが選ぶ同じ同型を使う。

## 使われ方
元のfull envelopeの指定された導来比較を、元の通常係数写像と照合する。
-/

public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B)
variable (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (f : OrientedPrism.Hom P Q)
variable (r n : ℕ) (κ κ' : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
variable (hκ' : cutoff B (prismPolynomialCompletion Q (Fin r)) ≤ κ')

/-- 元の完備テンソル比較は、元の純テンソルの係数像を保つ。 -/
theorem affineEnvelopeCompletedTensor_tmul :
    letI := f.toRingHom.toAlgebra
    let U := affineEnvelopeTerm P hP r n κ hκ
    let V := affineEnvelopeTerm Q hQ r n κ' hκ'
    letI := U.X.toHom.toRingHom.toAlgebra
    let e := (exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n
      κ κ' hκ hκ').choose
    ∀ (b : B) (c : U.X.B),
      e (pdCompletionUnit (B ⊗[A] U.X.B) p
        (algebraMap B (B ⊗[A] U.X.B) Q.generator) (b ⊗ₜ[A] c)) =
      V.X.toHom.toRingHom b * affineEnvelopeCoefficientMap f U V c := by
  let := f.toRingHom.toAlgebra
  let U := affineEnvelopeTerm P hP r n κ hκ
  let V := affineEnvelopeTerm Q hQ r n κ' hκ'
  let := U.X.toHom.toRingHom.toAlgebra
  let T := B ⊗[A] U.X.B
  letI := prismCompletedTensorCommRing (A := A) (C := U.X.B) Q
  let eH := exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n κ κ' hκ hκ'
  let e := eH.choose
  dsimp only
  intro b c
  have hs : (b ⊗ₜ[A] (1 : U.X.B)) * ((1 : B) ⊗ₜ[A] c) = b ⊗ₜ[A] c := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [← hs, map_mul, map_mul]
  change e (prismCompletedTensorLeft Q b) * e (prismCompletedTensorRight Q c) = _
  have hl : e (prismCompletedTensorLeft Q b) = V.X.toHom.toRingHom b :=
    RingHom.congr_fun eH.choose_spec.2 b
  have hr : e (prismCompletedTensorRight Q c) = affineEnvelopeCoefficientMap f U V c :=
    RingHom.congr_fun eH.choose_spec.1 c
  rw [hl, hr]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
