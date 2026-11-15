module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCompletionResidue
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineCompletedTensor

/-!
# 特定の結晶係数変更で使う完備テンソルの剰余

## 概要
結晶的な終域への元の実完備テンソルを p で割ると、通常テンソルの mod p を得る。

## 方針
既存の二座標完備化と p 完備化の環同型を、単位を保つ mod p の比較と合成する。

## 規約
両脚の値を指定する。平坦性や Tor 振幅はこの環同型には要求しない。

## 使われ方
Zp から特定の普遍結晶被覆への affine 項の比較。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
open SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable {p : ℕ} [Fact p.Prime] {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (Q : OrientedPrism p B) (hg : Q.generator = (p : B))
include hg

/-- 元の実完備テンソルの mod p は、両脚を保って通常テンソルの mod p と同型。 -/
theorem exists_crystallineTensorResidueEquiv :
    ∃ e : (PrismCompletedTensor (A := A) (C := C) Q ⧸
          Ideal.span {(p : PrismCompletedTensor (A := A) (C := C) Q)}) ≃+*
        ((B ⊗[A] C) ⧸ Ideal.span {(p : B ⊗[A] C)}),
      (∀ b : B, e (Ideal.Quotient.mk _ (prismCompletedTensorLeft Q b)) =
        Ideal.Quotient.mk _ (b ⊗ₜ[A] (1 : C))) ∧
      (∀ c : C, e (Ideal.Quotient.mk _ (prismCompletedTensorRight Q c)) =
        Ideal.Quotient.mk _ ((1 : B) ⊗ₜ[A] c)) := by
  let a := crystallineCompletedTensorRingEquiv (A := A) (C := C) Q hg
  have ha : Ideal.span {(p : CompletedRing p (B ⊗[A] C))} =
      (Ideal.span {(p : PrismCompletedTensor (A := A) (C := C) Q)}).map a.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let aq := Ideal.quotientEquiv _ _ a ha
  obtain ⟨e₀, he₀⟩ := exists_crystallineCompletionResidueEquiv (B ⊗[A] C) p
  refine ⟨aq.trans e₀, ?_, ?_⟩
  · intro b
    change e₀ (Ideal.Quotient.mk _ (a (prismCompletedTensorLeft Q b))) = _
    rw [show a (prismCompletedTensorLeft Q b) =
      principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[A] C)) (b ⊗ₜ[A] (1 : C))
      from crystallineCompletedTensorRingEquiv_left Q hg b]
    exact he₀ _
  · intro c
    change e₀ (Ideal.Quotient.mk _ (a (prismCompletedTensorRight Q c))) = _
    rw [show a (prismCompletedTensorRight Q c) =
      principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[A] C)) ((1 : B) ⊗ₜ[A] c)
      from crystallineCompletedTensorRingEquiv_right Q hg c]
    exact he₀ _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
