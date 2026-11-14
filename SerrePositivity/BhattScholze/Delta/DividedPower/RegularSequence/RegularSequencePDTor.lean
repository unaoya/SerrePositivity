module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePDPrimeRegular
public import SerrePositivity.BhattScholze.Delta.DividedPower.Coefficients.Factorial
public import SerrePositivity.HomologicalAlgebra.TorAlgebraScalarComparison
import Mathlib.RingTheory.Localization.BaseChange

/-!
# 分冪表示の高次 Tor の消滅

## 概要
BS 著者版 Lemma 2.38 の押し出しは、高次 Tor が消える。

## 方針
表示関係は p の剰余で Koszul 正則。p を反転すると一次分冪は自由な多項式変数なので、
局所化しても Koszul 正則になる。この二つを通常の Koszul 複体で合わせる。

## 規約
正則性は有限 Koszul 正則列。Tor は通常の可換環上で計算する。

## 使われ方
分冪包の離散性の古典的な形。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)

local notation "G" => DividedPowerAlgebra A (Fin r →₀ A)
local notation "L" => Localization.Away (p : A)
local notation "G₁" => DividedPowerAlgebra L (Fin r →₀ L)
local notation "T" => G ⊗[A] L
local notation "X" => (fun i : Fin r => (MvPolynomial.X i : MvPolynomial (Fin r) L))
local notation "γ[" i "]" => DividedPowerAlgebra.dp A 1 (Finsupp.single i 1 : Fin r →₀ A)
local notation "x" => (fun i : Fin r => γ[i] - algebraMap A G (f i))

/-- 概要：分冪表示環は係数多項式環上の通常の押し出し。
方針：係数への評価をモニック関係の商で表し、商とテンソルを交換する。
規約：多項式変数は一方で指定係数、他方で一次分冪に写る（BS 著者版 Lemma 2.38）。
使われ方：分冪包を計算する高次 Tor と次数零の環の対応。 -/
def dpFamilyPresentation_polynomialTensorEquiv :
    let P := MvPolynomial (Fin r) A
    letI : Algebra P A := (MvPolynomial.aeval f).toRingHom.toAlgebra
    letI : Algebra P G := (MvPolynomial.aeval (fun j : Fin r => γ[j])).toRingHom.toAlgebra
    G ⊗[P] A ≃ₐ[G] DPFamilyPresentation f := by
  let P := MvPolynomial (Fin r) A
  letI : Algebra P A := (MvPolynomial.aeval f).toRingHom.toAlgebra
  letI : Algebra P G := (MvPolynomial.aeval (fun j : Fin r => γ[j])).toRingHom.toAlgebra
  let z (j : Fin r) : P := MvPolynomial.X j - MvPolynomial.C (f j)
  let I := Ideal.span (Set.range z)
  have he : I.map (algebraMap P G) = dpFamilyRelationIdeal f := by
    simp only [I, Ideal.map_span, dpFamilyRelationIdeal, ← Set.range_comp']
    apply congrArg (fun y : Fin r → G => Ideal.span (Set.range y))
    funext j
    change MvPolynomial.aeval (fun k : Fin r => γ[k]) (z j) = x j
    simp [z]
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : G ≃ₐ[G] G)
      (evaluationRelationsQuotientAlgEquiv f).symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot G I).symm.trans
      (Ideal.quotientEquivAlgOfEq G he))

private theorem freeDPPolynomialEval_surjective (B : Type u) [CommRing B] [Algebra ℚ B] :
    Function.Surjective (freeDPPolynomialEval (Fin r) B B) := by
  let η : MvPolynomial (Fin r) B →ₐ[B] DividedPowerAlgebra B (Fin r →₀ B) :=
    MvPolynomial.aeval
    (fun i : Fin r => DividedPowerAlgebra.dp B 1 (Finsupp.single i 1 : Fin r →₀ B))
  have h : (freeDPPolynomialEval (Fin r) B B).comp η = AlgHom.id B _ := by
    ext i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, freeDPPolynomialEval_dp]
    simp
  intro y
  exact ⟨η y, DFunLike.congr_fun h y⟩

private theorem dpFamilyRelations_away_isKoszulResolution
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    IsKoszulResolution (algebraMap G T ∘ x) := by
  letI : Algebra ℚ L := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  let h₁ := (Algebra.TensorProduct.comm A G L).toRingEquiv.trans
    (freeDPBaseChangeEquiv (Fin r) A L).toRingEquiv
  let h₂ := AlgEquiv.ofBijective (freeDPPolynomialEval (Fin r) L L)
    ⟨freeDPPolynomialEval_injective (Fin r) L L (by simpa using Function.injective_id),
      freeDPPolynomialEval_surjective L⟩
  let e := h₁.trans h₂.toRingEquiv
  have hγ (i : Fin r) : e (algebraMap G T γ[i]) = X i := by
    change h₂ (freeDPBaseChangeEquiv (Fin r) A L (1 ⊗ₜ[A] γ[i])) = X i
    rw [freeDPBaseChangeEquiv_dp]
    change freeDPPolynomialEval (Fin r) L L
      (DividedPowerAlgebra.dp L 1 (Finsupp.single i 1)) = X i
    rw [freeDPPolynomialEval_dp]
    simp
  have hc (a : A) : e (algebraMap G T (algebraMap A G a)) =
      MvPolynomial.C (algebraMap A L a) := by
    change h₂ (h₁ (algebraMap A T a)) = _
    have hc₁ : h₁ (algebraMap A T a) = algebraMap L G₁ (algebraMap A L a) := by
      change freeDPBaseChangeEquiv (Fin r) A L (1 ⊗ₜ[A] algebraMap A G a) = _
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
      exact (freeDPBaseChangeEquiv (Fin r) A L).commutes (algebraMap A L a)
    rw [hc₁, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]
  apply isKoszulResolution_of_ringEquiv e
  have he : e.toRingHom ∘ algebraMap G T ∘ x =
      fun i => X i - MvPolynomial.C (algebraMap A L (f i)) := by
    funext i
    change e (algebraMap G T (γ[i] - algebraMap A G (f i))) = _
    rw [map_sub, map_sub]
    exact congrArg₂ (· - ·) (hγ i) (hc (f i))
  rw [he]
  exact evaluationRelations_regular (algebraMap A L ∘ f)

/-- 概要：分冪表示の一次関係の Koszul 複体は通常商の分解。
方針：mod p の Koszul 計算と、p を反転したときのモニック一次関係を合わせる。
規約：BS 著者版 Lemma 2.38 の有限 Koszul 正則列。
使われ方：高次 Tor の消滅。 -/
theorem dpFamilyRelations_isKoszulResolution
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hp : IsSMulRegular A (p : A))
    (hf : IsKoszulResolution (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘ f)) :
    IsKoszulResolution x := by
  letI : IsLocalization.Away (p : G) T := by
    rw [← map_natCast (algebraMap A G)]
    infer_instance
  exact isKoszulResolution_of_snoc_and_away x (p : G)
    (dpFamilyRelations_snoc_isKoszulResolution f hp hf)
    (dpFamilyRelations_away_isKoszulResolution f hlocal)

/-- 概要：分冪包の押し出しを計算する通常の高次 Tor は零。
方針：多項式環から係数環への Koszul 分解を、自由分冪代数に係数拡大する。
規約：BS 著者版 Lemma 2.38 の離散性の古典的な形。
使われ方：正則列に沿う分冪包の底変換。 -/
theorem dpFamilyPresentation_tor_subsingleton
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hp : IsSMulRegular A (p : A))
    (hf : IsKoszulResolution (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘ f))
    (i : ℕ) :
    let P := MvPolynomial (Fin r) A
    letI : Algebra P A := (MvPolynomial.aeval f).toRingHom.toAlgebra
    letI : Algebra P G := (MvPolynomial.aeval (fun j : Fin r => γ[j])).toRingHom.toAlgebra
    Subsingleton (TorAlg (algebraMap P G) (i+1) A) := by
  let P := MvPolynomial (Fin r) A
  letI : Algebra P A := (MvPolynomial.aeval f).toRingHom.toAlgebra
  letI : Algebra P G := (MvPolynomial.aeval (fun j : Fin r => γ[j])).toRingHom.toAlgebra
  let z (j : Fin r) : P := MvPolynomial.X j - MvPolynomial.C (f j)
  have hz : IsKoszulResolution z := evaluationRelations_regular f
  let e₀ := (evaluationRelationsQuotientAlgEquiv f).toLinearEquiv
  have e₁ := algebraKoszulTorComparison (C := G) z hz (i+1)
  have he : algebraMap P G ∘ z = x := by
    funext j
    change MvPolynomial.aeval (fun k : Fin r => γ[k]) (z j) = x j
    simp [z]
  rw [he] at e₁
  have hZ := ModuleCat.isZero_iff_subsingleton.mp
    ((dpFamilyRelations_isKoszulResolution f hlocal hp hf).isZero (-(↑(i+1) : ℤ)) (by omega))
  letI : Subsingleton ((ModuleCat.restrictScalars (algebraMap P G)).obj
      ((koszulComplex x).homology (-(↑(i+1) : ℤ)))) := hZ
  let e₂ := torAlgebraComparison (C := G) (ModuleCat.of P A) (i+1)
  let F := (Tor (ModuleCat P) (i+1)).obj (ModuleCat.of P G)
  exact (e₂.symm ≪≫ (F.mapIso e₀.toModuleIso).symm ≪≫ e₁).toLinearEquiv.injective.subsingleton

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.38"] _root_.SerrePositivity.BhattScholze.dpFamilyPresentation_tor_subsingleton
