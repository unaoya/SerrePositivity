module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Tactic.Ring

/-! # 1 の原始三乗根を添加する二次代数

## 概要

三次の円分多項式 `cubicCyclotomicPolynomial R` = X² + X + 1 を添加した代数 `CubicCyclotomicAlgebra R` とその根 `cubicCyclotomicRoot` を与え、根の関係式から ζ³ = 1 と (1 - ζ)(1 - ζ²) = 3 を示す。局所環の剰余体で 2 = 0 なら 3 は単元で、したがって 1 - ζ と 1 - ζ² も単元である。剰余体で 2 = 0 のとき、X² + X + 1 はモニックな既約因子 g とその余因子 h に互いに素に分解する。

## 方針

多項式は Mathlib の `Polynomial.cyclotomic 3 R` の abbrev とし、計算は `Polynomial.cyclotomic_three` で X² + X + 1 に戻して行う。互いに素な分解は、2 = 0 なら導関数が 1 になることから、積の導関数の式 g'h + gh' = 1 を Bézout の式として読む。

## 規約

`cubicCyclotomicPolynomial`・`CubicCyclotomicAlgebra` は IntersectionMultiplicity・PerfectComplex が名前で参照する。`cube_eq_one_of_cubic_relation` は KTheory/Adams・PerfectComplex の Cubic* で広く使う。

## 使われ方

PerfectComplex/CubicActionDecomposition と Cubic* 群（位数 3 の作用の固有分解）、KTheory/Adams、`CubicCyclotomic/LocalExtension`。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity
open Polynomial IsLocalRing

section Algebra

variable (R : Type u) [CommRing R]

/-- 三次の円分多項式 X² + X + 1。 -/
abbrev cubicCyclotomicPolynomial : R[X] := cyclotomic 3 R

lemma cubicCyclotomicPolynomial_eq : cubicCyclotomicPolynomial R = X ^ 2 + X + 1 :=
  cyclotomic_three R

lemma cubicCyclotomicPolynomial_natDegree [Nontrivial R] :
    (cubicCyclotomicPolynomial R).natDegree = 2 := by
  rw [cubicCyclotomicPolynomial_eq, add_assoc, natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · rw [← C_1, natDegree_X_add_C]
    simp

abbrev CubicCyclotomicAlgebra := AdjoinRoot (cubicCyclotomicPolynomial R)

instance cubicCyclotomicAlgebra_nontrivial [Nontrivial R] :
    Nontrivial (CubicCyclotomicAlgebra R) := by
  apply (AdjoinRoot.nontrivial_iff_of_monic (cyclotomic.monic 3 R)).mpr
  rw [degree_eq_natDegree (cyclotomic.monic 3 R).ne_zero, cubicCyclotomicPolynomial_natDegree R]
  norm_num

def cubicCyclotomicRoot : CubicCyclotomicAlgebra R :=
  AdjoinRoot.root (cubicCyclotomicPolynomial R)

instance cubicCyclotomicAlgebra_free : Module.Free R (CubicCyclotomicAlgebra R) :=
  (cyclotomic.monic 3 R).free_adjoinRoot

instance cubicCyclotomicAlgebra_finite : Module.Finite R (CubicCyclotomicAlgebra R) :=
  (cyclotomic.monic 3 R).finite_adjoinRoot

instance cubicCyclotomicAlgebra_flat : Module.Flat R (CubicCyclotomicAlgebra R) :=
  Module.Flat.of_free

lemma cubicCyclotomicRoot_relation :
    cubicCyclotomicRoot R ^ 2 + cubicCyclotomicRoot R + 1 = 0 := by
  have h : AdjoinRoot.mk (cubicCyclotomicPolynomial R) (X ^ 2 + X + 1) = 0 := by
    rw [← cubicCyclotomicPolynomial_eq]
    exact AdjoinRoot.mk_self
  simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_one, cubicCyclotomicRoot] using h

end Algebra

section Relation

variable {R : Type u} [CommRing R]

/-- 関係式 t² + t + 1 = 0 から、任意の可換環で t³ = 1 が従う。 -/
lemma cube_eq_one_of_cubic_relation (t : R) (ht : t ^ 2 + t + 1 = 0) : t ^ 3 = 1 := by
  calc
    t ^ 3 = (t - 1) * (t ^ 2 + t + 1) + 1 := by ring
    _ = 1 := by rw [ht]; ring

/-- 1 との二つの差の積は 3 に等しい。混標数でも成り立つ。 -/
lemma one_sub_mul_one_sub_sq_of_cubic_relation (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (1 - t) * (1 - t ^ 2) = 3 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  calc
    (1 - t) * (1 - t ^ 2) = t ^ 3 + 2 - (t ^ 2 + t + 1) := by ring
    _ = 3 := by rw [hc, ht]; ring

lemma isUnit_three_of_residue_two_eq_zero [IsLocalRing R]
    (h : (2 : ResidueField R) = 0) : IsUnit (3 : R) := by
  apply (residue_ne_zero_iff_isUnit (3 : R)).mp
  have he : (3 : ResidueField R) = 1 := by
    calc
      (3 : ResidueField R) = 2 + 1 := by norm_num
      _ = 1 := by rw [h]; simp
  simpa only [map_ofNat, he] using (one_ne_zero : (1 : ResidueField R) ≠ 0)

lemma isUnit_one_sub_of_cubic_relation (t : R) (ht : t ^ 2 + t + 1 = 0)
    (hthree : IsUnit (3 : R)) : IsUnit (1 - t) ∧ IsUnit (1 - t ^ 2) := by
  have hm : IsUnit ((1 - t) * (1 - t ^ 2)) :=
    (one_sub_mul_one_sub_sq_of_cubic_relation t ht).symm ▸ hthree
  exact ⟨isUnit_of_mul_isUnit_left hm, isUnit_of_mul_isUnit_right hm⟩

end Relation

section Fiber

variable {K : Type u} [Field K]

lemma cubicCyclotomicPolynomial_derivative (htwo : (2 : K) = 0) :
    (cubicCyclotomicPolynomial K).derivative = 1 := by
  rw [cubicCyclotomicPolynomial_eq]
  simp only [derivative_add, derivative_X_pow, derivative_X, derivative_one, Nat.cast_ofNat,
    htwo, C_0, zero_mul, zero_add, add_zero]

/-- 2 = 0 の体では、モニックな既約因子とその余因子は互いに素である（因子が一次でも二次でも）。 -/
lemma exists_cubicCyclotomic_coprime_factor (htwo : (2 : K) = 0) :
    ∃ g h : K[X], g.Monic ∧ Irreducible g ∧
      cubicCyclotomicPolynomial K = g * h ∧ IsCoprime g h ∧ IsField (AdjoinRoot g) := by
  have hnu : ¬ IsUnit (cubicCyclotomicPolynomial K) := by
    intro hu
    have hd := natDegree_eq_zero_of_isUnit hu
    rw [cubicCyclotomicPolynomial_natDegree K] at hd
    omega
  obtain ⟨g, hg, hi, hdvd⟩ := exists_monic_irreducible_factor (cubicCyclotomicPolynomial K) hnu
  obtain ⟨h, hh⟩ := hdvd
  have hd : g.derivative * h + g * h.derivative = 1 := by
    rw [← derivative_mul, ← hh]
    exact cubicCyclotomicPolynomial_derivative htwo
  refine ⟨g, h, hg, hi, hh, ?_, (AdjoinRoot.isField_iff_irreducible).mpr hi⟩
  refine ⟨h.derivative, g.derivative, ?_⟩
  calc
    h.derivative * g + g.derivative * h = g.derivative * h + g * h.derivative := by ring
    _ = 1 := hd

end Fiber

end SerrePositivity
