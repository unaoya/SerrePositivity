module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelCompletionQuotient
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
## 概要
有限段の分冪係数の底変換を、係数イデアルによる商へ移す。

## 方針
未完備模型の底変換同型を代数同型として読み、テンソル積と商の比較を使う。

## 規約
可換環のk代数lと有限段数r,nを固定し、テンソル積をl ⊗[k] RawKの順序で書く。

## 使われ方
有限段の分冪係数の模型を、係数環の商へ底変換する構成に用いる。
-/

public noncomputable section

open Algebra.TensorProduct
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (k l : Type u) [CommRing k] [CommRing l] [Algebra k l] (r n : ℕ)

local notation "RawK" => pdRaw k r n
local notation "RawL" => pdRaw l r n

/-- 未完備の分冪係数変更の底変換同型。 -/
def pdRawCoefficients_baseChangeAlgEquiv : l ⊗[k] RawK ≃ₐ[l] RawL := by
  let h := pdRawCoefficients_isBaseChange k l r n
  refine AlgEquiv.ofLinearEquiv h.equiv ?_ ?_
  · change h.equiv ((1 : l) ⊗ₜ[k] (1 : RawK)) = 1
    rw [h.equiv_tmul, one_smul]
    exact map_one (pdRawCoefficients k l r n)
  · apply LinearMap.map_mul_of_map_mul_tmul
    intro a b x y
    change h.equiv ((a * b) ⊗ₜ[k] (x * y)) =
      h.equiv (a ⊗ₜ[k] x) * h.equiv (b ⊗ₜ[k] y)
    rw [h.equiv_tmul, h.equiv_tmul, h.equiv_tmul]
    change (a * b) • pdRawCoefficients k l r n (x * y) =
      (a • pdRawCoefficients k l r n x) * (b • pdRawCoefficients k l r n y)
    simp only [map_mul, Algebra.smul_def]
    ring

@[simp]
theorem pdRawCoefficients_baseChangeAlgEquiv_tmul (a : l) (x : RawK) :
    pdRawCoefficients_baseChangeAlgEquiv k l r n (a ⊗ₜ[k] x) =
      a • pdRawCoefficients k l r n x :=
  (pdRawCoefficients_isBaseChange k l r n).equiv_tmul a x

/-- 係数をイデアルで割ってからの底変換は、底変換済み分冪環の商で表される。 -/
def pdRawCoefficients_quotientTensorEquiv (I : Ideal l) :
    ((l ⧸ I) ⊗[k] RawK) ≃+* (RawL ⧸ (I.map (algebraMap l RawL))) := by
  let e := pdRawCoefficients_baseChangeAlgEquiv k l r n
  refine (Algebra.TensorProduct.quotientTensorEquiv (R := k) k RawK l I).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ e.toRingEquiv ?_)
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext (fun a => (e.commutes a).symm)

theorem pdRawCoefficients_quotientTensorEquiv_tmul (I : Ideal l) (a : l) (x : RawK) :
    pdRawCoefficients_quotientTensorEquiv k l r n I (Ideal.Quotient.mk I a ⊗ₜ[k] x) =
      Ideal.Quotient.mk (I.map (algebraMap l RawL)) (a • pdRawCoefficients k l r n x) := by
  unfold pdRawCoefficients_quotientTensorEquiv
  rw [RingEquiv.trans_apply]
  change Ideal.quotientEquiv _ _ (pdRawCoefficients_baseChangeAlgEquiv k l r n).toRingEquiv _
    (Ideal.Quotient.mk _ (a ⊗ₜ[k] x)) = _
  rw [Ideal.quotientEquiv_mk]
  exact congrArg (Ideal.Quotient.mk (I.map (algebraMap l RawL)))
    (pdRawCoefficients_baseChangeAlgEquiv_tmul k l r n a x)

end SerrePositivity.BhattScholze.Prismatic
