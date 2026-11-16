module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.TensorScalarQuotient
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineResidueAlgebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction

/-!
# 元の向き付き係数射の被覆上の剰余行の代数比較

## 概要
終域の生成元がpである元のprism射について、元の剰余行の通常係数拡大を計算する。

## 方針
係数拡大先でdとpの像が同伴であることを使い、元の商テンソルを既存の結晶剰余項へ移す。

## 規約
始域の生成元がpであるとは仮定しない。元の単位純テンソルの像を明示する。

## 使われ方
HT04の標準行射の同型性を、元の係数射を保つ代数同型で検査する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B))

include hg
/-- 元のdとpの係数像は、終域が結晶的なとき同伴である。 -/
theorem affineCoefficient_generator_associated_prime :
    Associated (f.toRingHom P.generator) (f.toRingHom (p : A)) := by
  obtain ⟨v, hv, _⟩ := f.existsUnique_generator_unit
  rw [hv, hg, map_natCast]
  exact (show Associated (p : B) ((p : B) * (v : B)) from ⟨v, rfl⟩).symm

include hg
/-- 元の剰余行の通常係数拡大は、元の単位純テンソルを保って終域の剰余行と同型。 -/
theorem exists_affineOrientedRowBaseChangeEquiv (r : ℕ) (n : SimplexCategory) :
    letI := f.toRingHom.toAlgebra
    letI : Algebra A ((reducedModel P hP r).obj n) :=
      ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
    letI : Algebra B ((reducedModel Q hQ r).obj n) :=
      ((affineBaseCoefficients Q hQ r).app n).hom.toAlgebra
    ∃ e : (B ⊗[A] (reducedModel P hP r).obj n) ≃ₐ[B] (reducedModel Q hQ r).obj n,
      ∀ x : (reducedModel P hP r).obj n, e ((1 : B) ⊗ₜ[A] x) =
        (affineHTCoefficientReducedAny f hP hQ r).app n x := by
  letI := f.toRingHom.toAlgebra
  letI : Algebra A ((reducedModel P hP r).obj n) :=
    ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
  letI : Algebra B ((reducedModel Q hQ r).obj n) :=
    ((affineBaseCoefficients Q hQ r).app n).hom.toAlgebra
  let U := affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl
  let V := affineEnvelopeTerm Q hQ r n.len (cutoff B (affineAlgebra Q r)) le_rfl
  letI := U.X.toHom.toRingHom.toAlgebra
  letI := ((Ideal.Quotient.mk V.X.Q.ideal).comp V.X.toHom.toRingHom).toAlgebra
  let ψ := U.X.toHom.toRingHom
  let eP : (reducedModel P hP r).obj n ≃ₐ[A] (U.X.B ⧸ Ideal.span {ψ P.generator}) := by
    change (U.X.B ⧸ Ideal.span {(ψ P.generator) ^ (1 : ℕ)}) ≃ₐ[A] _
    exact Ideal.quotientEquivAlgOfEq A (by simp only [pow_one])
  let eQ : (reducedModel Q hQ r).obj n ≃ₐ[B] (V.X.B ⧸ V.X.Q.ideal) :=
    { __ := htResidueIso Q hQ r n
      commutes' := fun _ => rfl }
  have hψ : ψ (p : A) = (p : U.X.B) := map_natCast ψ p
  letI : Algebra A (U.X.B ⧸ Ideal.span {(p : U.X.B)}) := inferInstance
  let eN : (U.X.B ⧸ Ideal.span {ψ (p : A)}) ≃ₐ[A]
      (U.X.B ⧸ Ideal.span {(p : U.X.B)}) :=
    Ideal.quotientEquivAlgOfEq A (congrArg (fun c : U.X.B => Ideal.span {c}) hψ)
  let eS := (tensorScalarQuotientEquiv f.toRingHom ψ P.generator (p : A)
    (affineCoefficient_generator_associated_prime f hg)).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eN)
  obtain ⟨e, he⟩ := HTUniversalCrystallineInput.exists_affineCrystallineResidueTermAlgEquiv
    P Q f hP hQ hg r n.len (cutoff A (affineAlgebra P r))
      (cutoff B (affineAlgebra Q r)) le_rfl le_rfl
  let t := Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eP
  refine ⟨t.trans (eS.trans (e.trans eQ.symm)), ?_⟩
  intro x
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (eP x)
  have hx : x = eP.symm (Ideal.Quotient.mk _ c) := by
    rw [hc, AlgEquiv.symm_apply_apply]
  rw [hx]
  apply eQ.injective
  change eQ (eQ.symm (e (eS ((1 : B) ⊗ₜ[A]
    eP (eP.symm (Ideal.Quotient.mk _ c)))))) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have heS : eS ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk _ c) =
      (1 : B) ⊗ₜ[A] (Ideal.Quotient.mk (Ideal.span {(p : U.X.B)}) c) := by
    dsimp only [eS, AlgEquiv.trans_apply]
    rw [tensorScalarQuotientEquiv_tmul]
    change (1 : B) ⊗ₜ[A] eN (Ideal.Quotient.mk _ c) = _
    erw [Ideal.quotientEquivAlgOfEq_mk]
  rw [heS, he]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
