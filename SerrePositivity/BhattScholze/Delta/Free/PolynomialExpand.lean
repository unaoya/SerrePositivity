module

public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Tactic
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# 多項式の expand 写像に沿う自由性

## 概要
多項式環 R[x] は expand 写像 x ↦ xⁿ に沿って自由加群で、基底は各指数が n 未満の単項式。忠実平坦性も。
BS 著者版 Lemma 2.11 の Frobenius の平坦性に使う、多項式の指数拡大を調べる。

## 方針
指数を n で割った商と余りへの分解で単項式を付け替える。

## 規約
δ 環とは無関係な可換環論。BS だけが使うので当面ここに置く（CommutativeAlgebra への移動は別に判断）。

## 使われ方
自由 δ 環の Frobenius の平坦性、André（MonicPowerFamilyCover）。
-/

@[expose] public noncomputable section
universe u v

/-! ## 多項式の指数の商と余り

各変数の指数をnで割り、n未満の有限台指数と商指数に分解する。
多項式のexpand射の加群基底を構成するためのBS専用計算。
-/

section PolynomialExponentDivMod

namespace SerrePositivity.BhattScholze

/-- 各指数がn未満の有限台指数。 -/
abbrev PolynomialExponentRemainder (n : ℕ) (σ : Type u) :=
  {d : σ →₀ ℕ // ∀ s, d s < n}

/-- 有限台指数の各座標の商と余りによる同値。任意個の変数を含む。 -/
def polynomialExponentDivModEquiv (n : ℕ) (σ : Type u) (hn : 0 < n) :
    (σ →₀ ℕ) ≃ PolynomialExponentRemainder n σ × (σ →₀ ℕ) where
  toFun d := (⟨d.mapRange (fun k ↦ k % n) (Nat.zero_mod n),
    fun s ↦ by simpa using Nat.mod_lt (d s) hn⟩,
    d.mapRange (fun k ↦ k / n) (Nat.zero_div n))
  invFun x := n • x.2 + x.1.val
  left_inv d := by
    ext s
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul]
    exact Nat.div_add_mod (d s) n
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      ext s
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (x.1.property s)]
    · ext s
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul]
      rw [Nat.mul_add_div hn, Nat.div_eq_of_lt (x.1.property s), add_zero]

/-- 商・余りから元の指数を復元する式。 -/
@[simp] theorem polynomialExponentDivModEquiv_symm_apply
    (n : ℕ) (σ : Type u) (hn : 0 < n)
    (b : PolynomialExponentRemainder n σ) (q : σ →₀ ℕ) :
    (polynomialExponentDivModEquiv n σ hn).symm (b, q) = n • q + b.val := rfl

end SerrePositivity.BhattScholze

end PolynomialExponentDivMod

/-! ## expand射の単項式分解

指数の商・余りの同値で係数を付け替え、Mathlibのcurryでまとめる。
まだexpandを係数環とする自由加群の構造とは区別する。
-/

section PolynomialExpandDecomposition

namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R] (hn : 0 < n)

/-- 各指数がn未満の単項式で分類した、多項式の係数分解。 -/
def polynomialExpandDecomposition :
    MvPolynomial σ R ≃ₗ[R] PolynomialExponentRemainder n σ →₀ MvPolynomial σ R :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans
    ((Finsupp.lcongr (polynomialExponentDivModEquiv n σ hn) (LinearEquiv.refl R R)).trans
      ((Finsupp.curryLinearEquiv R).trans
        (Finsupp.lcongr (Equiv.refl _) (AddMonoidAlgebra.coeffLinearEquiv R).symm)))

/-- 逆分解は、余りbと商qの単項式をn*q+bの単項式へ戻す。 -/
@[simp] theorem polynomialExpandDecomposition_symm_single_monomial
    (b : PolynomialExponentRemainder n σ) (q : σ →₀ ℕ) (c : R) :
    (polynomialExpandDecomposition n σ R hn).symm
      (Finsupp.single b (MvPolynomial.monomial q c)) =
      MvPolynomial.monomial (n • q + b.val) c := by
  change (AddMonoidAlgebra.coeffLinearEquiv R).symm
    ((Finsupp.lcongr (polynomialExponentDivModEquiv n σ hn) (LinearEquiv.refl R R)).symm
      ((Finsupp.curryLinearEquiv R).symm
        ((Finsupp.lcongr (Equiv.refl (PolynomialExponentRemainder n σ))
          (AddMonoidAlgebra.coeffLinearEquiv R).symm).symm
            (Finsupp.single b (MvPolynomial.monomial q c))))) = _
  rw [Finsupp.lcongr_symm_single]
  change (AddMonoidAlgebra.coeffLinearEquiv R).symm
    ((Finsupp.lcongr (polynomialExponentDivModEquiv n σ hn) (LinearEquiv.refl R R)).symm
      ((Finsupp.curryLinearEquiv R).symm (Finsupp.single b (Finsupp.single q c)))) = _
  simp only [Finsupp.curryLinearEquiv_symm_apply, Finsupp.uncurry_single,
    Finsupp.lcongr_symm_single, polynomialExponentDivModEquiv_symm_apply]
  rfl

end SerrePositivity.BhattScholze

end PolynomialExpandDecomposition

/-! ## 多項式expand射の自由性

Mathlibのexpand射によるスカラー作用を、標準ULift型で通常の係数加群と区別する。
整数の自由δ環の混標数Frobeniusの平坦性とは別のmod p計算。
-/

section PolynomialExpandFree

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- expand作用を持つ加群の型名。台環はMathlibの標準ULift多項式環。 -/
def PolynomialExpandTarget (_n : ℕ) (σ : Type u) (R : Type v) [CommRing R] :=
  ULift.{0} (MvPolynomial σ R)

instance polynomialExpandTargetCommRing : CommRing (PolynomialExpandTarget n σ R) := by
  unfold PolynomialExpandTarget
  infer_instance

/-- expand射によるスカラー作用。標準型ULiftで係数環の通常作用と区別する。 -/
abbrev polynomialExpandAlgebra : Algebra (MvPolynomial σ R) (PolynomialExpandTarget n σ R) :=
  (((ULift.ringEquiv : PolynomialExpandTarget n σ R ≃+* MvPolynomial σ R).symm.toRingHom).comp
    (MvPolynomial.expand n).toRingHom).toAlgebra

attribute [local instance] polynomialExpandAlgebra

/-- 指数がn未満の単項式の、expandによるスカラー作用に関する線形結合。 -/
def polynomialExpandCombination :
    (PolynomialExponentRemainder n σ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      PolynomialExpandTarget n σ R :=
  Finsupp.linearCombination (MvPolynomial σ R) (fun b ↦ ULift.up (MvPolynomial.monomial b.val 1))

/-- 線形結合の単項式上の式。 -/
@[simp] theorem polynomialExpandCombination_single_monomial
    (b : PolynomialExponentRemainder n σ) (q : σ →₀ ℕ) (c : R) :
    polynomialExpandCombination n σ R (Finsupp.single b (MvPolynomial.monomial q c)) =
      ULift.up (MvPolynomial.monomial (n • q + b.val) c) := by
  rw [polynomialExpandCombination, Finsupp.linearCombination_single]
  apply (ULift.ringEquiv : PolynomialExpandTarget n σ R ≃+* MvPolynomial σ R).injective
  change MvPolynomial.expand n (MvPolynomial.monomial q c) *
    MvPolynomial.monomial b.val 1 = MvPolynomial.monomial (n • q + b.val) c
  rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_mul_monomial, mul_one]

/-- 線形結合は、係数の商・余り分解の逆射そのものである。 -/
theorem polynomialExpandCombination_eq_decomposition_symm (hn : 0 < n)
    (f : PolynomialExponentRemainder n σ →₀ MvPolynomial σ R) :
    (polynomialExpandCombination n σ R f).down =
      (polynomialExpandDecomposition n σ R hn).symm f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, map_add]
    change (polynomialExpandCombination n σ R f).down +
      (polynomialExpandCombination n σ R g).down = _
    rw [hf, hg]
  | single b a =>
    induction a using MvPolynomial.induction_on' with
    | add a a' ha ha' =>
      rw [Finsupp.single_add, map_add, map_add]
      change (polynomialExpandCombination n σ R (Finsupp.single b a)).down +
        (polynomialExpandCombination n σ R (Finsupp.single b a')).down = _
      rw [ha, ha']
    | monomial q c =>
      rw [polynomialExpandCombination_single_monomial,
        polynomialExpandDecomposition_symm_single_monomial]

/-- n>0なら、expand作用に関する単項式線形結合は全単射。 -/
theorem polynomialExpandCombination_bijective (hn : 0 < n) :
    Function.Bijective (polynomialExpandCombination n σ R) := by
  have he := polynomialExpandCombination_eq_decomposition_symm n σ R hn
  constructor
  · intro f g h
    apply (polynomialExpandDecomposition n σ R hn).symm.injective
    rw [← he f, ← he g, h]
  · intro x
    refine ⟨polynomialExpandDecomposition n σ R hn x.down, ?_⟩
    apply ULift.ext
    rw [he, LinearEquiv.symm_apply_apply]

/-- expand作用を持つ多項式環の具体的な単項式基底。 -/
def polynomialExpandBasis (hn : 0 < n) :
    Module.Basis (PolynomialExponentRemainder n σ) (MvPolynomial σ R)
      (PolynomialExpandTarget n σ R) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (polynomialExpandCombination n σ R)
    (polynomialExpandCombination_bijective n σ R hn)).symm

/-- expand作用を持つ多項式環は自由加群。 -/
theorem polynomialExpand_moduleFree (hn : 0 < n) :
    Module.Free (MvPolynomial σ R) (PolynomialExpandTarget n σ R) :=
  Module.Free.of_basis (polynomialExpandBasis n σ R hn)

/-- expand作用を持つ多項式環は平坦。 -/
theorem polynomialExpand_moduleFlat (hn : 0 < n) :
    Module.Flat (MvPolynomial σ R) (PolynomialExpandTarget n σ R) := by
  let := polynomialExpand_moduleFree n σ R hn
  infer_instance

/-- 非零係数環ではexpand作用の多項式環は忠実平坦。 -/
theorem polynomialExpand_moduleFaithfullyFlat [Nontrivial R] (hn : 0 < n) :
    Module.FaithfullyFlat (MvPolynomial σ R) (PolynomialExpandTarget n σ R) := by
  let : Nontrivial (PolynomialExpandTarget n σ R) := by
    unfold PolynomialExpandTarget
    infer_instance
  let := polynomialExpand_moduleFree n σ R hn
  infer_instance

end SerrePositivity.BhattScholze

end PolynomialExpandFree
