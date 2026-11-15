module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineResidueTerms
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction

/-!
# 結晶 affine 項の同じ係数作用での比較

## 概要
元の両脚を保つ affine 剰余項の同型は、終域の基底環上の代数同型である。

## 方針
元の左脚の式を使って、検証済みの環同型に基底との可換式を添える。

## 規約
作用は終域の元の基底脚から取る。平坦性を要求しない項ごとの同型。

## 使われ方
標準の係数拡大の線形比較の同型性を、元の affine 項の環比較で確認する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B) (f : OrientedPrism.Hom P Q)
variable (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (hg : Q.generator = (p : B))
variable (r n : ℕ) (κ κ' : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
variable (hκ' : cutoff B (prismPolynomialCompletion Q (Fin r)) ≤ κ')
local notation "U" => affineEnvelopeTerm P hP r n κ hκ
local notation "V" => affineEnvelopeTerm Q hQ r n κ' hκ'
include hg

/-- 元の affine 項の同型は、終域の元の基底作用を保つ代数同型である。 -/
theorem exists_affineCrystallineResidueTermAlgEquiv :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    letI := ((Ideal.Quotient.mk (V).X.Q.ideal).comp (V).X.toHom.toRingHom).toAlgebra
    ∃ e : (B ⊗[A] ((U).X.B ⧸ Ideal.span {(p : (U).X.B)})) ≃ₐ[B]
        ((V).X.B ⧸ (V).X.Q.ideal),
      ∀ c : (U).X.B, e ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk _ c) =
        Ideal.Quotient.mk _ (affineEnvelopeCoefficientMap f U V c) := by
  letI := f.toRingHom.toAlgebra
  letI := (U).X.toHom.toRingHom.toAlgebra
  letI := ((Ideal.Quotient.mk (V).X.Q.ideal).comp (V).X.toHom.toRingHom).toAlgebra
  obtain ⟨e, hl, hr⟩ := exists_affineCrystallineResidueTermEquiv
    P Q f hP hQ hg r n κ κ' hκ hκ'
  refine ⟨{ __ := e, commutes' := ?_ }, hr⟩
  intro b
  change e (b ⊗ₜ[A] (1 : (U).X.B ⧸ Ideal.span {(p : (U).X.B)})) =
    Ideal.Quotient.mk (V).X.Q.ideal ((V).X.toHom.toRingHom b)
  simpa only [map_one] using hl b

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
