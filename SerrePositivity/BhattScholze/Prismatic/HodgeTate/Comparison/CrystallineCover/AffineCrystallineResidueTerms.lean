module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineOrdinaryTensorResidue
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeBaseChangeCoefficients

/-!
# 結晶係数への元の affine 剰余項の底変換

## 概要
結晶的な終域について、元の affine 項の mod p を通常の係数拡大で計算する。

## 方針
元の完備テンソルの包への比較に、両脚を保つ完備テンソルの mod p 比較を合成する。

## 規約
始域と終域の有界性、終域の選択生成元 p、二つの濃度上限を明示する。

## 使われ方
特定の Zp 係数射の Hodge–Tate 剰余模型の、指定された項ごとの比較。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B) (f : OrientedPrism.Hom P Q)
variable (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (hg : Q.generator = (p : B))
variable (r n : ℕ) (κ κ' : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
variable (hκ' : cutoff B (prismPolynomialCompletion Q (Fin r)) ≤ κ')
local notation "U" => affineEnvelopeTerm P hP r n κ hκ
local notation "V" => affineEnvelopeTerm Q hQ r n κ' hκ'
include hg

/-- 結晶係数への affine 項の比較は、元の二つの脚を保つ環同型である。 -/
theorem exists_affineCrystallineResidueTermEquiv :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    ∃ e : (B ⊗[A] ((U).X.B ⧸ Ideal.span {(p : (U).X.B)})) ≃+*
        ((V).X.B ⧸ (V).X.Q.ideal),
      (∀ b : B, e (b ⊗ₜ[A] Ideal.Quotient.mk _ (1 : (U).X.B)) =
        Ideal.Quotient.mk _ ((V).X.toHom.toRingHom b)) ∧
      (∀ c : (U).X.B, e ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk _ c) =
        Ideal.Quotient.mk _ (affineEnvelopeCoefficientMap f U V c)) := by
  letI := f.toRingHom.toAlgebra
  letI := (U).X.toHom.toRingHom.toAlgebra
  obtain ⟨a, har, hal⟩ := exists_affineEnvelopeCoefficientBaseChange_equiv
    P Q f hP hQ r n κ κ' hκ hκ'
  have ha : Ideal.span {(p : (V).X.B)} =
      (Ideal.span {(p : PrismCompletedTensor (A := A) (C := (U).X.B) Q)}).map a.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let aq := Ideal.quotientEquiv _ _ a ha
  have hV : Ideal.span {(p : (V).X.B)} = (V).X.Q.ideal := by
    simpa only [hg, map_natCast] using (V).X.toHom.span_map_generator
  let vq := Ideal.quotEquivOfEq hV
  obtain ⟨e₀, he₀l, he₀r⟩ :=
    exists_crystallineOrdinaryTensorResidueEquiv (A := A) (C := (U).X.B) p Q hg
  refine ⟨e₀.trans (aq.trans vq), ?_, ?_⟩
  · intro b
    change vq (aq (e₀ (b ⊗ₜ[A] Ideal.Quotient.mk _ (1 : (U).X.B)))) = _
    rw [he₀l]
    change Ideal.Quotient.mk _ (a (prismCompletedTensorLeft Q b)) = _
    exact congrArg (Ideal.Quotient.mk (V).X.Q.ideal) (RingHom.congr_fun hal b)
  · intro c
    change vq (aq (e₀ ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk _ c))) = _
    rw [he₀r]
    change Ideal.Quotient.mk _ (a (prismCompletedTensorRight Q c)) = _
    exact congrArg (Ideal.Quotient.mk (V).X.Q.ideal) (RingHom.congr_fun har c)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
