module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineTensorResidue
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# 結晶係数での通常テンソル商と実完備テンソル商

## 概要
通常の係数拡大後の mod p と、元の結晶完備テンソルの mod p を比較する。

## 方針
通常テンソルと商の既存の同型に、両脚を保つ実完備化の剰余比較を合成する。

## 規約
同型は元の二つの係数射を保つ。平坦性の仮定は使わない。

## 使われ方
特定の Zp 係数射による affine 剰余項の比較を構成する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] (p : ℕ)

/-- 通常の係数拡大と mod p 商の指定された比較。 -/
def ordinaryTensorModPEquiv :
    (B ⊗[A] (C ⧸ Ideal.span {(p : C)})) ≃+*
      ((B ⊗[A] C) ⧸ Ideal.span {(p : B ⊗[A] C)}) := by
  let I : Ideal C := Ideal.span {(p : C)}
  let a := (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B C B I).toRingEquiv
  have hi : I.map (Algebra.TensorProduct.includeRight (A := B) (R := A)).toRingHom =
      Ideal.span {(p : B ⊗[A] C)} := by
    rw [show I = Ideal.span {(p : C)} from rfl,
      Ideal.map_span, Set.image_singleton, map_natCast]
  exact a.trans (Ideal.quotEquivOfEq hi)

/-- 通常テンソル商の比較は、元の純テンソルの剰余を与える。 -/
theorem ordinaryTensorModPEquiv_tmul (b : B) (c : C) :
    ordinaryTensorModPEquiv (A := A) p (b ⊗ₜ[A] Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk _ (b ⊗ₜ[A] c) := by
  rfl

variable [Fact p.Prime] (Q : OrientedPrism p B) (hg : Q.generator = (p : B))
include hg

/-- 通常の係数拡大した mod p は、元の結晶完備テンソルの mod p と両脚を保って同型。 -/
theorem exists_crystallineOrdinaryTensorResidueEquiv :
    ∃ e : (B ⊗[A] (C ⧸ Ideal.span {(p : C)})) ≃+*
        (PrismCompletedTensor (A := A) (C := C) Q ⧸
          Ideal.span {(p : PrismCompletedTensor (A := A) (C := C) Q)}),
      (∀ b : B, e (b ⊗ₜ[A] Ideal.Quotient.mk _ (1 : C)) =
        Ideal.Quotient.mk _ (prismCompletedTensorLeft Q b)) ∧
      (∀ c : C, e ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk _ c) =
        Ideal.Quotient.mk _ (prismCompletedTensorRight Q c)) := by
  obtain ⟨a, ha, hb⟩ := exists_crystallineTensorResidueEquiv (A := A) (C := C) Q hg
  refine ⟨(ordinaryTensorModPEquiv (A := A) p).trans a.symm, ?_, ?_⟩
  · intro b
    apply a.injective
    change a (a.symm (ordinaryTensorModPEquiv (A := A) p _)) = _
    rw [RingEquiv.apply_symm_apply, ordinaryTensorModPEquiv_tmul, ha]
  · intro c
    apply a.injective
    change a (a.symm (ordinaryTensorModPEquiv (A := A) p _)) = _
    rw [RingEquiv.apply_symm_apply, ordinaryTensorModPEquiv_tmul, hb]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
