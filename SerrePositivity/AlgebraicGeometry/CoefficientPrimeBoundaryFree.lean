module

public import SerrePositivity.AlgebraicGeometry.CoefficientPrimeBoundaryGeneration
public import SerrePositivity.AlgebraicGeometry.LocalRegularMinorPureFree

/-!
概要：KST §5、Stacks 0810 の係数中心の特別な局所環における純変換の自由性。
方針：係数イデアルの正則単項化と高次小行列式の消滅を完全な表示の基底変更へ適用する。
規約：小行列式の共通因子と元の境界を区別し、両者の正則性を確認する。
使われ方：係数 blowup の特別な局所環で純変換の自由性と階数を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：係数イデアルが正則単項となる拡大素点で境界純変換は予期した階数の自由加群。
方針：係数の正則単項化、境界の正則性、任意の基底変更後の表示の完全性を局所自由性判定へ渡す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、次次数の小行列式の消滅を元の行列に仮定する。
使われ方：一般有限型加群の係数中心による平坦化の局所自由性入力。
-/
theorem coefficient_prime_boundary_free_and_finrank
    {A B C M ι m n : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [AddCommGroup M] [Module B M] [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (H : Matrix m n B) (k : ℕ) (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q)
    (hzero : matrixMinorIdeal H (k + 1) = ⊥)
    (c f : C) (hc : IsRegular c) (hf : IsRegular f) (N : ℕ) (hcf : c ∣ f ^ N)
    (hcoeff : (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k)).map (algebraMap A C) =
      Ideal.span {c}) (P : Ideal C) (hP : P ≠ ⊤) [(P.map (algebraMap C (C ⊗[A] B))).IsPrime] :
    let D := C ⊗[A] B
    let L := Localization.AtPrime (P.map (algebraMap C D))
    let φ : B →+* L := (algebraMap D L).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom
    letI : Algebra B L := φ.toAlgebra
    Module.Free L
        (modulePureTransform (algebraMap D L (algebraMap C D f)) (L ⊗[B] M)) ∧
      Module.finrank L
          (modulePureTransform (algebraMap D L (algebraMap C D f)) (L ⊗[B] M)) =
        Fintype.card m - k := by
  classical
  let D := C ⊗[A] B
  let L := Localization.AtPrime (P.map (algebraMap C D))
  let ψ := algebraMap D L
  let φB : B →+* D := (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom
  let φ : B →+* L := ψ.comp φB
  let : Algebra B L := φ.toAlgebra
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  have hcoeff' : splitAlgebraCoefficientIdeal e' ((matrixMinorIdeal H k).map φB) = Ideal.span {c} :=
    (splitAlgebraCoefficientIdeal_baseChange e p hpe _).trans hcoeff
  have hloc := coefficientIdeal_regular_principal_at_extended_prime e' p' hs c
    ((matrixMinorIdeal H k).map φB) hc hcoeff' P hP
  let cL := ψ (algebraMap C D c)
  let fL := ψ (algebraMap C D f)
  have hcL : IsRegular cL := isRegular_iff_mem_nonZeroDivisors.mpr hloc.1
  have hfL : IsRegular fL := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap (S := L) (P.map (algebraMap C D)).primeCompl
      (isRegular_iff_mem_nonZeroDivisors.mp
        (algebraMap_isRegular_of_split_coefficients e' p' hs f hf))
  have hcfL : cL ∣ fL ^ N := by
    simpa only [RingHom.comp_apply, map_pow] using map_dvd (ψ.comp (algebraMap C D)) hcf
  have hminor : matrixMinorIdeal (H.map (algebraMap B L)) k = Ideal.span {cL} := by
    rw [← matrixMinorIdeal_map H k (algebraMap B L)]
    change (matrixMinorIdeal H k).map (ψ.comp φB) = Ideal.span {cL}
    rw [← Ideal.map_map]
    exact hloc.2
  have hzeroL : matrixMinorIdeal (H.map (algebraMap B L)) (k + 1) = ⊥ := by
    rw [← matrixMinorIdeal_map, hzero, Ideal.map_bot]
  let qL := finiteFreePresentationBaseChange (C := L) q
  have hqL : Function.Surjective qL := finiteFreePresentationBaseChange_surjective q hq
  have hker := finiteFreePresentationBaseChange_columnSpan_eq_ker (C := L) H q hq hH
  exact boundaryPureTransform_free_and_finrank_of_regular_minorIdeal
    (H.map (algebraMap B L)) k cL fL hcL hfL N hcfL qL hqL hker hminor hzeroL

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
