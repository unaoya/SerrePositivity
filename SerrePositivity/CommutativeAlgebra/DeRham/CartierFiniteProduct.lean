module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteRepresentative
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteRepresentative
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierFinite
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight
import all SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
public import SerrePositivity.CommutativeAlgebra.DeRham.CohomologyWedge
import all SerrePositivity.CommutativeAlgebra.DeRham.CohomologyWedge
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
public import SerrePositivity.HomologicalAlgebra.CochainProductClass
import all SerrePositivity.HomologicalAlgebra.CochainProductClass

/-!
# 有限 Cartier の代表形式と外積

## 概要
Cartier の代表形式を取る線形写像は外積を保つ。

## 方針
単項式外積の台が重なると積は零。台が交わらなければ Cartier 指数は加法的。

## 規約
外積基底の符号には台を併合する順列の符号を使う。

## 使われ方
有限 Cartier 同型の乗法性。
-/

public noncomputable section

open Set Set.powersetCard MvPolynomial SerrePositivity.HomologicalAlgebra
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

variable (K T : Type u) [Field K] [Fintype T] [LinearOrder T]

private abbrev E (i : ℕ) (s : powersetCard T i) :=
  (Pi.basisFun K T).exteriorPower i s

private theorem exteriorBasis_mul_eq_zero {i j : ℕ} (s : powersetCard T i) (t : powersetCard T j)
    (h : ¬Disjoint s.val t.val) :
    exteriorWedge K (T → K) i j (E K T i s) (E K T j t) = 0 := by
  apply Subtype.ext
  simpa only [E, exteriorWedge, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_zero,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe] using
    ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint K (Pi.basisFun K T) s t h

private theorem exteriorBasis_mul {i j : ℕ} (s : powersetCard T i) (t : powersetCard T j)
    (h : Disjoint s.val t.val) :
    exteriorWedge K (T → K) i j (E K T i s) (E K T j t) =
      ((permOfDisjoint h).sign : ℤˣ) • E K T (i + j) (disjUnion h) := by
  apply Subtype.ext
  simp only [Units.smul_def]
  change _ = (⋀[K]^(i+j) (T → K)).subtype
    ((↑(permOfDisjoint h).sign : ℤ) • E K T (i+j) (disjUnion h))
  rw [map_zsmul]
  simpa only [E, exteriorWedge, LinearMap.coe_mk, AddHom.coe_mk, Submodule.subtype_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe, Units.smul_def] using
    ExteriorAlgebra.ιMulti_family_mul_of_disjoint K (Pi.basisFun K T) s t h

private theorem wedge_basis_eq_zero {i j : ℕ} (m n : T →₀ ℕ)
    (s : powersetCard T i) (t : powersetCard T j) (h : ¬Disjoint s.val t.val) :
    wedge K T (polynomialFormsBasis K T i (m,s)) (polynomialFormsBasis K T j (n,t)) = 0 := by
  simp only [polynomialFormsBasis, Module.Basis.tensorProduct_apply', coe_basisMonomials]
  rw [wedge_tmul, exteriorBasis_mul_eq_zero K T s t h, TensorProduct.tmul_zero]

private theorem wedge_basis {i j : ℕ} (m n : T →₀ ℕ)
    (s : powersetCard T i) (t : powersetCard T j) (h : Disjoint s.val t.val) :
    wedge K T (polynomialFormsBasis K T i (m,s)) (polynomialFormsBasis K T j (n,t)) =
      ((permOfDisjoint h).sign : ℤˣ) • polynomialFormsBasis K T (i+j) (m+n, disjUnion h) := by
  simp only [polynomialFormsBasis, Module.Basis.tensorProduct_apply', coe_basisMonomials]
  rw [wedge_tmul, exteriorBasis_mul K T s t h, monomial_mul_monomial, one_mul]
  simp only [Units.smul_def]
  exact map_zsmul (TensorProduct.mk K _ _ (monomial (m+n) 1)) _ _

omit [Field K] [Fintype T] in
private theorem cartierExponent_disjUnion (p : ℕ) {i j : ℕ}
    (m n : T →₀ ℕ) (s : powersetCard T i) (t : powersetCard T j) (h : Disjoint s.val t.val) :
    cartierExponent T p (m+n) (disjUnion h) =
      cartierExponent T p m s + cartierExponent T p n t := by
  ext x
  simp only [Finsupp.add_apply, cartierExponent_apply, powersetCard.disjUnion,
    Finset.mem_disjUnion, Nat.mul_add]
  have hh := Finset.disjoint_left.mp h
  by_cases hs : x ∈ s.val <;> by_cases ht : x ∈ t.val
  · exact (hh hs ht).elim
  all_goals simp [hs, ht] <;> omega

private theorem cartierRep_wedge_basis (p : ℕ) (hp : 0 < p) {i j : ℕ}
    (m n : T →₀ ℕ) (s : powersetCard T i) (t : powersetCard T j) :
    cartierRep K T p hp (i+j)
        (wedge K T (polynomialFormsBasis K T i (m,s)) (polynomialFormsBasis K T j (n,t))) =
      wedge K T (cartierRep K T p hp i (polynomialFormsBasis K T i (m,s)))
        (cartierRep K T p hp j (polynomialFormsBasis K T j (n,t))) := by
  rw [rep_basis, rep_basis]
  change cartierRep K T p hp (i+j)
        (wedge K T (polynomialFormsBasis K T i (m,s)) (polynomialFormsBasis K T j (n,t))) =
      wedge K T (polynomialFormsBasis K T i (cartierExponent T p m s,s))
        (polynomialFormsBasis K T j (cartierExponent T p n t,t))
  by_cases h : Disjoint s.val t.val
  · rw [wedge_basis K T m n s t h, wedge_basis K T _ _ s t h]
    simp only [Units.smul_def, map_zsmul, rep_basis]
    change _ • polynomialFormsBasis K T (i+j)
      (cartierExponent T p (m+n) (disjUnion h), disjUnion h) = _
    rw [cartierExponent_disjUnion T p m n s t h]
  · rw [wedge_basis_eq_zero K T m n s t h, wedge_basis_eq_zero K T _ _ s t h, map_zero]

private theorem cartierRep_wedge (p : ℕ) (hp : 0 < p) {i j : ℕ}
    (x : forms K T i) (y : forms K T j) :
    cartierRep K T p hp (i+j) (wedge K T x y) =
      wedge K T (cartierRep K T p hp i x) (cartierRep K T p hp j y) := by
  let W := fun i j => TensorProduct.map₂ (LinearMap.mul K (Poly K T))
    (exteriorWedge K (T → K) i j)
  let L := (W i j).compr₂ (cartierRep K T p hp (i+j))
  let R := (W i j).compl₁₂ (cartierRep K T p hp i) (cartierRep K T p hp j)
  have h : L = R := by
    apply (polynomialFormsBasis K T i).ext
    rintro ⟨m,s⟩
    apply (polynomialFormsBasis K T j).ext
    rintro ⟨n,t⟩
    exact cartierRep_wedge_basis K T p hp m n s t
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

set_option backward.isDefEq.respectTransparency false in
/-- 有限 Cartier の加法同型は de Rham コホモロジーの外積を保つ。 -/
theorem finiteCartierLinearEquiv_wedge (p : ℕ) [CharP K p] (hp : 0 < p) {i j : ℕ}
    (x : forms K T i) (y : forms K T j) :
    finiteCartierLinearEquiv K T p hp (i+j) (wedge K T x y) =
      deRhamCohomologyWedge K T (finiteCartierLinearEquiv K T p hp i x)
        (finiteCartierLinearEquiv K T p hp j y) := by
  rw [finiteCartierLinearEquiv_class, finiteCartierLinearEquiv_class, finiteCartierLinearEquiv_class]
  change CochainProduct.closedClass (i+j)
      (deRhamTerm K T (i+j) (cartierRep K T p hp (i+j) (wedge K T x y))) _ =
    (deRhamCochainWedge K T).onHomology
      (CochainProduct.closedClass i (deRhamTerm K T i (cartierRep K T p hp i x)) _)
      (CochainProduct.closedClass j (deRhamTerm K T j (cartierRep K T p hp j y)) _)
  have h := CochainProduct.onHomology_closedClass (deRhamCochainWedge K T)
    (deRhamTerm K T i (cartierRep K T p hp i x))
    (deRhamTerm K T j (cartierRep K T p hp j y)) (DFunLike.congr_fun (rep_d_zero K T p hp i) x)
    (DFunLike.congr_fun (rep_d_zero K T p hp j) y)
  have hw : deRhamTerm K T (i+j) (cartierRep K T p hp (i+j) (wedge K T x y)) =
      (deRhamCochainWedge K T).mul i j
        (deRhamTerm K T i (cartierRep K T p hp i x))
        (deRhamTerm K T j (cartierRep K T p hp j y)) :=
    congrArg (deRhamTerm K T (i+j)) (cartierRep_wedge K T p hp x y)
  have hc := DFunLike.congr_fun (rep_d_zero K T p hp (i+j)) (wedge K T x y)
  change (deRhamComplex K T).d (i+j) (i+j+1)
      (deRhamTerm K T (i+j) (cartierRep K T p hp (i+j) (wedge K T x y))) = 0 at hc
  rw [hw] at hc
  refine Eq.trans ?_ (h hc).symm
  generalize_proofs hleft hright
  congr 1


end SerrePositivity.DeRham
