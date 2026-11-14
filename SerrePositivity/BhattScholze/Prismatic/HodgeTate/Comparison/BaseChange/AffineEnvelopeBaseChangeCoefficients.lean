module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineEnvelopeCoefficients

/-!
# affine 包の完備底変換と指定された係数変更

## 概要
完備テンソル積からの affine 比較の右脚は、普遍性で指定した係数変更に一致する。

## 方針
δ 構造、基底脚と各頂点での像を確認し、包の一意性を適用する。

## 規約
比較の環同型の選択には依存しない右脚の等式を残す。

## 使われ方
BS 著者版 Proposition 3.13 (2) と Theorem 6.4 の厳密な余単体写像の底変換。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (P' : OrientedPrism p B) (f : OrientedPrism.Hom P P')
variable (hP : IsBoundedPrism P) (hP' : IsBoundedPrism P') (r n : ℕ)
variable (κ κ' : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
variable (hκ' : cutoff B (prismPolynomialCompletion P' (Fin r)) ≤ κ')

local notation "U" => affineEnvelopeTerm P hP r n κ hκ
local notation "V" => affineEnvelopeTerm P' hP' r n κ' hκ'

/-- 完備テンソル積による affine 包の同型は、指定された係数変更を計算する。 -/
theorem exists_affineEnvelopeCoefficientBaseChange_equiv :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    ∃ e : PrismCompletedTensor (A := A) (C := (U).X.B) P' ≃+* (V).X.B,
      e.toRingHom.comp (prismCompletedTensorRight P') = affineEnvelopeCoefficientMap f U V ∧
      e.toRingHom.comp (prismCompletedTensorLeft P') = (V).X.toHom.toRingHom := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  obtain ⟨e, hδ, hl, hx⟩ := exists_affineEnvelopeBaseChange_equiv
    P P' f r n hP hP' κ κ' hκ hκ'
  refine ⟨e, affineEnvelopeCoefficientMap_unique f U V _ hδ ?_ hx, hl⟩
  apply RingHom.ext
  intro a
  change e (prismCompletedTensorRight P' ((U).X.toHom.toRingHom a)) =
    (V).X.toHom.toRingHom (f.toRingHom a)
  have h := RingHom.congr_fun (prismCompletedTensor_square (A := A) (C := (U).X.B) P') a
  change prismCompletedTensorLeft P' (f.toRingHom a) =
    prismCompletedTensorRight P' ((U).X.toHom.toRingHom a) at h
  rw [← h]
  exact RingHom.congr_fun hl _

end SerrePositivity.BhattScholze.Prismatic
