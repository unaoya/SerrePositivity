module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteRepresentative
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteRepresentative
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierFinite
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives

/-!
# 有限 Cartier 同型の零次・一次の値

## 概要
零次の Frobenius と一次の座標類を、有限 Cartier の加法同型と照合する。

## 方針
零次は多項式単項式基底で比較し、一次では外積基底の一元集合を使う。

## 規約
零次の比較では係数の Frobenius が恒等であると仮定する。

## 使われ方
多項式 Hodge–Tate 比較の生成元。
-/

public noncomputable section

open CategoryTheory Set MvPolynomial
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

variable (K T : Type u) [Field K] [Fintype T] [LinearOrder T]
variable (p : ℕ) [CharP K p] (hp : 0 < p)

private def emptySupport : powersetCard T 0 :=
  ⟨∅, rfl⟩

private def singletonSupport (t : T) : powersetCard T 1 :=
  ⟨{t}, by simp⟩

private theorem polynomialFormsBasis_zero (m : T →₀ ℕ) :
    polynomialFormsBasis K T 0 (m, emptySupport T) = formsZeroEquiv K T (monomial m 1) := by
  rw [polynomialFormsBasis, Module.Basis.tensorProduct_apply', coe_basisMonomials,
    formsZeroEquiv_tmul]
  congr 1
  apply Subtype.ext
  simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe,
    ExteriorAlgebra.ιMulti_apply, exteriorPower.zeroEquiv]

private theorem polynomialFormsBasis_one (m : T →₀ ℕ) (t : T) :
    polynomialFormsBasis K T 1 (m, singletonSupport T t) =
      (monomial m 1 : Poly K T) • dX K T t := by
  rw [polynomialFormsBasis, Module.Basis.tensorProduct_apply', coe_basisMonomials]
  change monomial m 1 ⊗ₜ[K] _ = ((monomial m 1 : Poly K T) * 1) ⊗ₜ[K] _
  rw [mul_one]
  congr 1
  have h (i : Fin 1) : powersetCard.ofFinEmbEquiv.symm (singletonSupport T t) i = t := by
    have hm := (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (singletonSupport T t)
      (powersetCard.ofFinEmbEquiv.symm (singletonSupport T t) i)).mp ⟨i, rfl⟩
    simpa [singletonSupport] using hm
  apply Subtype.ext
  simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe, Function.comp_def, h,
    Pi.basisFun_apply, exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply]

omit [Fintype T] in
private theorem cartierExponent_empty (m : T →₀ ℕ) :
    cartierExponent T p m (emptySupport T) = p • m := by
  ext t
  simp [cartierExponent_apply, emptySupport]

omit [Fintype T] in
private theorem cartierExponent_singleton (t : T) :
    cartierExponent T p 0 (singletonSupport T t) = Finsupp.single t (p - 1) := by
  ext s
  by_cases h : s = t
  · subst s
    simp [cartierExponent_apply, singletonSupport]
  · simp [cartierExponent_apply, singletonSupport, h]

/-- Cartier の一次の座標類は X の p−1 乗を係数に持つ。 -/
theorem finiteCartierLinearEquiv_dX (t : T) :
    finiteCartierLinearEquiv K T p hp 1 (dX K T t) = cartierOneClass K T p t := by
  have hx : polynomialFormsBasis K T 1 (0, singletonSupport T t) = dX K T t := by
    rw [polynomialFormsBasis_one, monomial_zero', map_one, one_smul]
  rw [← hx, finiteCartierLinearEquiv_basis]
  unfold cartierOneClass
  congr 1
  rw [polynomialFormsBasis_one, cartierExponent_singleton, ← X_pow_eq_monomial]

omit [CharP K p] in
private theorem cartierRep_zero_monomial (m : T →₀ ℕ) :
    cartierRep K T p hp 0 (formsZeroEquiv K T (monomial m 1)) =
      formsZeroEquiv K T ((monomial m 1) ^ p) := by
  rw [← polynomialFormsBasis_zero K T m, rep_basis]
  change polynomialFormsBasis K T 0 (cartierExponent T p m (emptySupport T), emptySupport T) = _
  rw [polynomialFormsBasis_zero, cartierExponent_empty, monomial_pow, one_pow]

/-- Cartier の零次の像は、係数の Frobenius が恒等なら多項式の p 乗の類。 -/
theorem finiteCartierLinearEquiv_zero [Fact p.Prime] (hF : ∀ c : K, c ^ p = c) (f : Poly K T) :
    finiteCartierLinearEquiv K T p hp 0 (formsZeroEquiv K T f) =
      cartierZeroClass K T p (CharP.cast_eq_zero K p) f := by
  let F : Poly K T →ₗ[K] Poly K T :=
    { toAddHom := (frobenius (Poly K T) p).toAddMonoidHom
      map_smul' := fun c x => by
        change (c • x) ^ p = c • x ^ p
        simp [Algebra.smul_def, mul_pow, ← map_pow, hF] }
  have he : (cartierRep K T p hp 0).comp (formsZeroEquiv K T).toLinearMap =
      (formsZeroEquiv K T).toLinearMap.comp F := by
    apply (basisMonomials T K).ext
    intro m
    change cartierRep K T p hp 0 (formsZeroEquiv K T (monomial m 1)) =
      formsZeroEquiv K T ((monomial m 1) ^ p)
    exact cartierRep_zero_monomial K T p hp m
  rw [finiteCartierLinearEquiv_class]
  unfold cartierZeroClass
  congr 1
  exact DFunLike.congr_fun he f

end SerrePositivity.DeRham
