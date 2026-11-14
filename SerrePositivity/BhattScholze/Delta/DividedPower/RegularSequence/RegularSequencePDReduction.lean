module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePD

/-!
# 分冪表示の mod p

## 概要
有限族に沿う分冪表示の通常の mod p を係数の mod p 上の表示に同定する。

## 方針
通常商とテンソルの比較を、分冪包と δ 除算包の比較 の係数拡大同型に合成する。

## 規約
正則性はこの表示の比較には不要（BS 著者版 Lemma 2.38）。

## 使われ方
Construction 6.1 の結晶被覆の剰余を計算する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct

variable {A : Type u} [CommRing A] (p : ℕ) {r : ℕ} (f : Fin r → A)

/-- 概要：分冪表示の mod p は還元した族の分冪表示。
方針：通常商を係数商とのテンソルに直して 分冪包と δ 除算包の比較 の底変換を使う。
規約：BS 著者版 Lemma 2.38、Construction 6.1 の通常の環。
使われ方：p 完備化の剰余との比較。 -/
def dpFamilyModPrimeEquiv :
    (DPFamilyPresentation f ⧸ Ideal.span {(p : DPFamilyPresentation f)}) ≃+*
      DPFamilyPresentation (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘ f) := by
  let I : Ideal A := Ideal.span {(p : A)}
  let h : I.map (algebraMap A (DPFamilyPresentation f)) =
      Ideal.span {(p : DPFamilyPresentation f)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact (Ideal.quotEquivOfEq h.symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor (DPFamilyPresentation f) I).toRingEquiv.trans
      (dpFamilyBaseChangeEquiv (B := A ⧸ I) f).toRingEquiv)

/-- 概要：mod p の比較同型は係数の標準射を保つ。
方針：商テンソルの標準脚と底変換の代数上の性質を使う。
規約：BS 著者版 Construction 6.1 の式 (6) の最後の係数脚。
使われ方：Frobenius で捻った射の分解の照合。 -/
theorem dpFamilyModPrimeEquiv_coeff (a : A) :
    dpFamilyModPrimeEquiv p f
      (Ideal.Quotient.mk _ (algebraMap A (DPFamilyPresentation f) a)) =
      algebraMap (A ⧸ Ideal.span {(p : A)})
        (DPFamilyPresentation (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘ f))
        (Ideal.Quotient.mk _ a) := by
  unfold dpFamilyModPrimeEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply]
  change dpFamilyBaseChangeEquiv (B := A ⧸ Ideal.span {(p : A)}) f
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (DPFamilyPresentation f)
      (Ideal.span {(p : A)} )
        (algebraMap (A ⧸ Ideal.span {(p : A)}) _ (Ideal.Quotient.mk _ a))) = _
  rw [AlgEquiv.commutes, AlgEquiv.commutes]
  rfl

end SerrePositivity.BhattScholze
