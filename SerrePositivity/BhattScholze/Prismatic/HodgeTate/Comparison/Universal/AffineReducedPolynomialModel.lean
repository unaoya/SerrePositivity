module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletedPolynomialSplit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverCompleteness
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaResidue
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope

/-!
# 元の剰余行の完備自由多項式加群

## 概要
元の剰余行を、元の基底作用を保って完備自由多項式加群として読む。

## 方針
同じfull envelopeの基底生成元による商と、元の完備自由δ環の剰余公式を合成する。

## 規約
この項ごとの線形同型の自然性を仮定しない。Torの直和因子の検査だけに使う。

## 使われ方
元の完備形式を、検証済みの元の行の直和因子へ接続する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 同じ元の剰余行は、元の基底係数を保って完備自由多項式加群と同型。 -/
theorem exists_affineReducedCompletedPolynomialLinearEquiv (n : SimplexCategory) :
    let C := MvPolynomial (AffineIndex.{u} r n.len × ℕ) (A ⧸ P.ideal)
    let D := PrincipalCompletionH0 C (p : C)
    letI := principalCompletionCommRing C (p : C)
    letI := ((principalCompletionUnitRingHom C (p : C)).comp
      (MvPolynomial.C.comp (Ideal.Quotient.mk P.ideal))).toAlgebra
    Nonempty (((affineBaseModules P hP r).obj n) ≃ₗ[A] D) := by
  let S := AffineIndex.{u} r n.len
  let C := MvPolynomial (S × ℕ) (A ⧸ P.ideal)
  let D := PrincipalCompletionH0 C (p : C)
  letI := principalCompletionCommRing C (p : C)
  let g : A →+* D := (principalCompletionUnitRingHom C (p : C)).comp
    (MvPolynomial.C.comp (Ideal.Quotient.mk P.ideal))
  letI := g.toAlgebra
  let U := affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl
  let ψ := U.X.toHom.toRingHom
  have hψ : ψ = completedFreeDeltaBase P S := affineEnvelopeUnit_base P r n.len
  letI := ψ.toAlgebra
  letI : Algebra A ((reducedModel P hP r).obj n) :=
    ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
  let eP : (reducedModel P hP r).obj n ≃ₐ[A] (U.X.B ⧸ Ideal.span {ψ P.generator}) := by
    change (U.X.B ⧸ Ideal.span {(ψ P.generator) ^ (1 : ℕ)}) ≃ₐ[A]
      (U.X.B ⧸ Ideal.span {ψ P.generator})
    exact Ideal.quotientEquivAlgOfEq A (by simp only [pow_one])
  let eJ : (U.X.B ⧸ Ideal.span {ψ P.generator}) ≃+*
      (completedFreeDelta P S ⧸ Ideal.span {completedFreeDeltaBase P S P.generator}) :=
    Ideal.quotientEquiv _ _ (RingEquiv.refl _) (by
      change Ideal.span {completedFreeDeltaBase P S P.generator} =
        (Ideal.span {ψ P.generator}).map (RingHom.id _)
      rw [Ideal.map_id, hψ]
      rfl)
  let eR := eJ.trans (completedFreeDeltaResidueEquiv P S)
  let e := eP.toRingEquiv.trans eR
  have he (a : A) : e ((affineBaseCoefficients P hP r).app n a) = g a := by
    change eR (eP ((affineBaseCoefficients P hP r).app n a)) = g a
    have hPe : eP ((affineBaseCoefficients P hP r).app n a) =
        Ideal.Quotient.mk _ (ψ a) := eP.commutes a
    rw [hPe]
    change completedFreeDeltaResidueEquiv P S (eJ (Ideal.Quotient.mk _ (ψ a))) = g a
    erw [Ideal.quotientEquiv_mk]
    change completedFreeDeltaResidueEquiv P S (Ideal.Quotient.mk _ (ψ a)) = g a
    rw [hψ]
    change completedFreeDeltaResidueEquiv P S (Ideal.Quotient.mk _
      (pdCompletionUnit (RelativeFreeDeltaRing (R := A) S) p
        (algebraMap A _ P.generator) (MvPolynomial.C a))) =
      principalCompletionUnitRingHom C (p : C) (MvPolynomial.C (Ideal.Quotient.mk P.ideal a))
    have h := completedFreeDeltaResidueEquiv_unit P S (MvPolynomial.C a)
    simpa only [MvPolynomial.map_C] using h
  refine ⟨{ __ := e.toAddEquiv, map_smul' := ?_ }⟩
  intro a x
  change (reducedModel P hP r).obj n at x
  change e ((affineBaseCoefficients P hP r).app n a * x) = g a * e x
  rw [map_mul, he]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
