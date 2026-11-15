module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineReducedAlgebra
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineResidueAlgebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineReducedAlgebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineReducedModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 元の結晶 affine 剰余行の係数変更

## 概要
結晶的な二つの基底の間で、元の affine 剰余項の通常の係数拡大を計算する。

## 方針
元の mod p 表示、項ごとの代数同型、元の剰余表示への逆を合成する。

## 規約
終域の基底環の元の作用と、元の affineHTCoefficientReduced の値を保つ。

## 使われ方
特定の Zp 係数射の標準の完備導来底変換を、元の affine 剰余行へ接続する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hPg : P.generator = (p : A)) (hQg : Q.generator = (p : B))

include hPg hQg
/-- 二つの結晶的な選択生成元は、元の prism 射によって厳密に保たれる。 -/
theorem crystallineCoefficientGenerator_eq : f.toRingHom P.generator = Q.generator :=
  (congrArg f.toRingHom hPg).trans ((map_natCast f.toRingHom p).trans hQg.symm)

include hPg hQg
/-- 元の affine 剰余行の通常の係数拡大は、元の係数射を計算する代数同型。 -/
theorem exists_affineCrystallineRowBaseChangeEquiv (r : ℕ) (n : SimplexCategory) :
    letI := f.toRingHom.toAlgebra
    letI : Algebra A ((reducedModel P hP r).obj n) :=
      ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
    letI : Algebra B ((reducedModel Q hQ r).obj n) :=
      ((affineBaseCoefficients Q hQ r).app n).hom.toAlgebra
    ∃ e : (B ⊗[A] (reducedModel P hP r).obj n) ≃ₐ[B] (reducedModel Q hQ r).obj n,
      ∀ x : (reducedModel P hP r).obj n, e ((1 : B) ⊗ₜ[A] x) =
        (affineHTCoefficientReduced f hP hQ r
          (crystallineCoefficientGenerator_eq f hPg hQg)).app n x := by
  letI := f.toRingHom.toAlgebra
  letI : Algebra A ((reducedModel P hP r).obj n) :=
      ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
  letI : Algebra B ((reducedModel Q hQ r).obj n) :=
      ((affineBaseCoefficients Q hQ r).app n).hom.toAlgebra
  let U := affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl
  let V := affineEnvelopeTerm Q hQ r n.len (cutoff B (affineAlgebra Q r)) le_rfl
  letI := U.X.toHom.toRingHom.toAlgebra
  letI := ((Ideal.Quotient.mk V.X.Q.ideal).comp V.X.toHom.toRingHom).toAlgebra
  let eP : (reducedModel P hP r).obj n ≃ₐ[A]
      (U.X.B ⧸ Ideal.span {(p : U.X.B)}) :=
    affineCrystallineReducedTermAlgEquiv P hP r hPg n
  let eQ : (reducedModel Q hQ r).obj n ≃ₐ[B] (V.X.B ⧸ V.X.Q.ideal) :=
    { __ := htResidueIso Q hQ r n
      commutes' := fun _ => rfl }
  obtain ⟨e, he⟩ := exists_affineCrystallineResidueTermAlgEquiv
    P Q f hP hQ hQg r n.len (cutoff A (affineAlgebra P r))
      (cutoff B (affineAlgebra Q r)) le_rfl le_rfl
  let a := Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eP
  refine ⟨a.trans (e.trans eQ.symm), ?_⟩
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply eQ.injective
  change eQ (eQ.symm (e ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk _ c))) = _
  rw [AlgEquiv.apply_symm_apply, he]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
