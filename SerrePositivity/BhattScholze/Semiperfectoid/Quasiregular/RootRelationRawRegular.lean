module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilyFractionBasis
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationPolynomial
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# 生の有限根関係の Koszul 正則性

## 概要
通常変数の Xi−fi を根付き変数環へ移した有限列は Koszul 正則。
## 方針
小数指数基底による平坦性で通常多項式の弱正則列を移す。
## 規約
BS 著者版 Proposition 7.10 の完備化前の有限 T。p 正則性を仮定しない。
## 使われ方
有限関係の実完備化と包絡への移送。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Andre _root_.RingTheory.Sequence
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)
local notation "B" => rootFamilyRaw p R (Fin r)
local notation "Poly" => MvPolynomial (Fin r) R

/-- 生の根付き変数環は、通常多項式環上で自由。 -/
theorem rootFamilyRaw_polynomial_free :
    letI := (rootFamilyPolynomialMap p R (Fin r)).toAlgebra
    Module.Free Poly B := by
  letI := (rootFamilyPolynomialMap p R (Fin r)).toAlgebra
  exact Module.Free.of_basis (rootFamilyFractionBasis p R (Fin r))

/-- Xi−fi の像の列は、生の根付き変数環上で弱正則。 -/
theorem rootRelationRaw_isWeaklyRegular :
    RingTheory.Sequence.IsWeaklyRegular B
      (List.ofFn ((rootFamilyPolynomialMap p R (Fin r)) ∘ rootRelationPolynomial R f)) := by
  letI := (rootFamilyPolynomialMap p R (Fin r)).toAlgebra
  letI := rootFamilyRaw_polynomial_free p R (r := r)
  have h : RingTheory.Sequence.IsWeaklyRegular Poly (List.ofFn (rootRelationPolynomial R f)) := by
    unfold rootRelationPolynomial
    have h' := monicRelation_fin_isWeaklyRegular
      (fun i : Fin r => Polynomial.X - Polynomial.C (f i))
      (fun i => Polynomial.monic_X_sub_C (f i)) (fun i : Fin r => i) Function.injective_id
    simpa only [monicRelation, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, rootRelationPolynomial] using h'
  have ht : RingTheory.Sequence.IsWeaklyRegular (Poly ⊗[Poly] B)
      (List.ofFn (rootRelationPolynomial R f)) := h.isWeaklyRegular_rTensor
  have hb := ((TensorProduct.lid Poly B).isWeaklyRegular_congr
    (List.ofFn (rootRelationPolynomial R f))).mp ht
  have hm := (isWeaklyRegular_map_algebraMap_iff (R := Poly) (S := B) B
    (List.ofFn (rootRelationPolynomial R f))).mpr hb
  have he : algebraMap Poly B = rootFamilyPolynomialMap p R (Fin r) := rfl
  rw [he] at hm
  simpa only [List.map_ofFn] using hm

/-- 概要：根付き変数環の Xi−fi の Koszul 複体は通常商の分解。
方針：弱正則性を既存の Koszul 分解の定理へ渡す。
規約：BS 著者版 Proposition 7.10 の有限 T の完備化前。
使われ方：有限関係商の実完備化の計算。 -/
theorem rootRelationRaw_isKoszulResolution :
    SerrePositivity.IsKoszulResolution
      ((rootFamilyPolynomialMap p R (Fin r)) ∘ rootRelationPolynomial R f) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _ (rootRelationRaw_isWeaklyRegular p R f)

end SerrePositivity.BhattScholze.Semiperfectoid
