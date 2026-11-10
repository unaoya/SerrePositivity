module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# 切断多項式環の単項式基底

## 概要
各変数の p 乗を殺した環は、各指数が p 未満の単項式を係数上の基底とする。

## 方針
単項式イデアルの所属条件で、剰余を低指数の係数の族と同一視する。

## 規約
p は任意の自然数。係数環に標数の仮定は置かない。

## 使われ方
自由分冪代数の mod p の表示（BS 著者版 Lemma 2.38）。
-/

public noncomputable section

open scoped Classical

universe u v

namespace SerrePositivity.BhattScholze

variable (R : Type u) [CommRing R] (σ : Type v) (p : ℕ)

/-- 概要：各座標の p 乗が生成する多項式イデアル。
方針：純冪単項式の族の生成イデアル。
規約：BS 著者版 Lemma 2.38 の剰余模型。
使われ方：切断多項式環。 -/
@[expose] def truncatedPolynomialIdeal : Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun s : σ => (MvPolynomial.X s : MvPolynomial σ R) ^ p)

/-- 概要：切断多項式環の基底添字。
方針：指数の有限台関数を、各座標が p 未満に制限する。
規約：BS 著者版 Lemma 2.38 の剰余模型。
使われ方：切断多項式環の基底と分冪の剰余ブロック。 -/
abbrev TruncatedMonomial := {m : σ →₀ ℕ // ∀ s, m s < p}

local notation "P" => MvPolynomial σ R
local notation "I" => truncatedPolynomialIdeal R σ p
local notation "D" => TruncatedMonomial σ p

private theorem truncatedPolynomialIdeal_mem (f : P) :
    f ∈ I ↔ ∀ m ∈ f.support, ¬∀ s, m s < p := by
  have he : Set.range (fun s : σ => (MvPolynomial.X s : P) ^ p) =
      (fun m => MvPolynomial.monomial m (1 : R)) '' Set.range (fun s : σ => Finsupp.single s p) := by
    rw [← Set.range_comp]
    simp only [Function.comp_def, MvPolynomial.X_pow_eq_monomial]
  rw [truncatedPolynomialIdeal, he, MvPolynomial.mem_ideal_span_monomial_image]
  apply forall₂_congr
  intro m _
  simp only [Set.exists_range_iff, Finsupp.single_le_iff, not_forall, not_lt]

private def lowPolynomialCoefficients : P →ₗ[R] D →₀ R :=
  (Finsupp.lsubtypeDomain {m : σ →₀ ℕ | ∀ s, m s < p}).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

private theorem lowPolynomialCoefficients_apply (f : P) (m : D) :
    lowPolynomialCoefficients R σ p f m = f.coeff m := rfl

private theorem lowPolynomialCoefficients_ker :
    (lowPolynomialCoefficients R σ p).ker = Submodule.restrictScalars R (I : Submodule P P) := by
  ext f
  rw [LinearMap.mem_ker, show (f ∈ Submodule.restrictScalars R (I : Submodule P P)) = (f ∈ I) from rfl,
    truncatedPolynomialIdeal_mem R σ p]
  constructor
  · intro h m hm hmp
    have hzero := congrArg (fun g : D →₀ R => g ⟨m, hmp⟩) h
    exact (MvPolynomial.mem_support_iff.mp hm) hzero
  · intro h
    ext m
    rw [lowPolynomialCoefficients_apply, Finsupp.zero_apply]
    exact MvPolynomial.notMem_support_iff.mp (fun hm => h m hm m.property)

private theorem lowPolynomialCoefficients_surjective :
    Function.Surjective (lowPolynomialCoefficients R σ p) := by
  intro z
  let g := (Finsupp.supportedEquivFinsupp (R := R) (M := R)
    {m : σ →₀ ℕ | ∀ s, m s < p}).symm z
  refine ⟨(AddMonoidAlgebra.coeffLinearEquiv R).symm g.val, ?_⟩
  change Finsupp.subtypeDomain _ ((AddMonoidAlgebra.coeffLinearEquiv R)
    ((AddMonoidAlgebra.coeffLinearEquiv R).symm g.val)) = z
  rw [LinearEquiv.apply_symm_apply]
  exact (Finsupp.supportedEquivFinsupp (R := R) _).apply_symm_apply z

/-- 概要：切断多項式環の加群座標は各指数が p 未満の単項式の係数。
方針：低指数への係数制限の核を切断イデアルに同定し、係数制限の全射性を使う。
規約：BS 著者版 Lemma 2.38 の mod p 模型。
使われ方：切断多項式環上の分冪ブロック基底。 -/
def truncatedPolynomialRepr : (P ⧸ I) ≃ₗ[R] D →₀ R :=
  (Submodule.quotEquivOfEq _ _ (lowPolynomialCoefficients_ker R σ p).symm).trans
      ((lowPolynomialCoefficients R σ p).quotKerEquivOfSurjective
        (lowPolynomialCoefficients_surjective R σ p))

/-- 概要：切断商の座標同型は、商にする前の低指数係数を返す。
方針：商同型の代表元の式を使う。
規約：BS 著者版 Lemma 2.38 の mod p 模型。
使われ方：単項式基底の比較。 -/
theorem truncatedPolynomialRepr_mk (f : P) (m : D) :
    truncatedPolynomialRepr R σ p (Ideal.Quotient.mk I f) m = f.coeff m := by
  change lowPolynomialCoefficients R σ p f m = _
  rfl

/-- 概要：切断多項式環の単項式基底。
方針：低指数係数の線形同型を基底の座標に取る。
規約：BS 著者版 Lemma 2.38 の mod p 模型。
使われ方：分冪代数を切断多項式環上の自由加群として計算する。 -/
def truncatedPolynomialBasis : Module.Basis D R (P ⧸ I) :=
  ⟨truncatedPolynomialRepr R σ p⟩

/-- 概要：切断多項式の基底ベクトルは単項式の剰余類。
方針：低指数の係数が対応する一座標だけ 1 であることを示す。
規約：BS 著者版 Lemma 2.38 の mod p 模型。
使われ方：分冪ブロックの基底ベクトルの像。 -/
theorem truncatedPolynomialBasis_apply (m : D) :
    truncatedPolynomialBasis R σ p m = Ideal.Quotient.mk I (MvPolynomial.monomial m 1) := by
  apply (truncatedPolynomialBasis R σ p).repr.injective
  rw [Module.Basis.repr_self]
  ext i
  rw [show (truncatedPolynomialBasis R σ p).repr = truncatedPolynomialRepr R σ p from rfl,
    truncatedPolynomialRepr_mk, MvPolynomial.coeff_monomial, Finsupp.single_apply]
  simp only [Subtype.ext_iff]

end SerrePositivity.BhattScholze
