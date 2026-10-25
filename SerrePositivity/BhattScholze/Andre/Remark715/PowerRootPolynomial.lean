module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootExponents
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# André E1・E2：無限 p 冪根多項式環の単項式基底

## 概要

p 冪分母を持つ非負有理数を指数とする加法モノイド環を構成する。
これは互換な変数 Yₙ、Yₙ₊₁ᵖ=Yₙ を持ち、全単項式は一つの有限段の変数の冪となる。
係数環上の具体的単項式基底を備える。
BS Rem 7.15（著者版 p.62）の R/ϖ[Y¹⸍ᵖ∞] の自由性の計算。

## 方針

指数の p 冪分母表示と既存の加法モノイド環の単項式基底を使う。
小数指数による通常多項式環上の分解と、モニック冪商への移送の準備である。

## 規約

係数環の標数・非零性・被約性は仮定しない。p の正値性だけを使う。
p 進完備化した環を定義するものではない。

## 使われ方

原典の pd 計算における未完備の無限 p 冪根多項式環の自由性を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)

/-- 概要：無限 p 冪根の一変数多項式環の具体的な単項式表示。
方針：非負 p 冪分母指数の加法モノイド環を使う。
規約：各元は有限個の指数だけを持つ。
使われ方：BS Rem 7.15（著者版 p.62）の未完備環 P。 -/
abbrev PowerRootPolynomial := AddMonoidAlgebra R (powerRootExponentMonoid p hp)

/-- 概要：互換な p 冪根変数 Yₙ。
方針：指数 1/pⁿ、係数 1 の単項式を取る。
規約：Y₀ が通常の変数に当たる。
使われ方：BS Rem 7.15（著者版 p.62）の有限段の包含。 -/
def powerRootPolynomialVariable (n : ℕ) : PowerRootPolynomial R p hp :=
  AddMonoidAlgebra.single (powerRootVariableExponent p hp n) 1

/-- 概要：構成した変数は Yₙ₊₁ᵖ=Yₙ を満たす。
方針：単項式の冪の公式と指数の p 倍の等式を使う。
規約：係数環に関する仮定は追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の無限 p 冪根の関係式。 -/
theorem powerRootPolynomialVariable_pow (n : ℕ) :
    powerRootPolynomialVariable R p hp (n + 1) ^ p = powerRootPolynomialVariable R p hp n := by
  simp only [powerRootPolynomialVariable, AddMonoidAlgebra.single_pow,
    powerRootVariableExponent_nsmul, one_pow]

/-- 概要：全ての単項式はある有限段の変数の冪と係数の積に書ける。
方針：指数の p 冪分母表示と単項式の冪の公式を使う。
規約：段は単項式ごとに選び、係数環の非零性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の有限段からの生成。 -/
theorem powerRootPolynomial_single_exists (q : powerRootExponentMonoid p hp) (a : R) :
    ∃ n k : ℕ, AddMonoidAlgebra.single q a =
      algebraMap R (PowerRootPolynomial R p hp) a * powerRootPolynomialVariable R p hp n ^ k := by
  obtain ⟨n, k, rfl⟩ := powerRootExponent_exists_nsmul p hp q
  refine ⟨n, k, ?_⟩
  rw [powerRootPolynomialVariable, AddMonoidAlgebra.single_pow, one_pow]
  simp [AddMonoidAlgebra.coe_algebraMap]

/-- 概要：無限 p 冪根多項式環の係数環上の単項式基底。
方針：加法モノイド環の標準基底を使う。
規約：指数型は p 冪分母の非負有理数そのもの。
使われ方：BS Rem 7.15（著者版 p.62）の P の自由性。 -/
def powerRootPolynomialBasis :
    Module.Basis (powerRootExponentMonoid p hp) R (PowerRootPolynomial R p hp) :=
  AddMonoidAlgebra.basis _ R

/-- 概要：構成した基底の各値は指数 q、係数 1 の単項式。
方針：標準加法モノイド環基底の値を取り出す。
規約：具体的な単項式表示を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の自由基底の計算。 -/
theorem powerRootPolynomialBasis_apply (q : powerRootExponentMonoid p hp) :
    powerRootPolynomialBasis R p hp q = AddMonoidAlgebra.single q 1 := rfl

/-- 概要：無限 p 冪根多項式環は元の係数環上自由。
方針：具体的単項式基底から自由性を得る。
規約：係数環の標数や p ねじれなしは要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の原典の通常代数計算。 -/
theorem powerRootPolynomial_free : Module.Free R (PowerRootPolynomial R p hp) :=
  Module.Free.of_basis (powerRootPolynomialBasis R p hp)

/-- 概要：互換な p 冪根変数の全体はこの環を係数環上生成する。
方針：各単項式をある段の変数の冪に書き、単項式の線形生成を使う。
規約：有限個の変数だけを固定して生成すると主張するものではない。
使われ方：BS Rem 7.15（著者版 p.62）の無限 p 冪根変数環の具体的表示。 -/
theorem powerRootPolynomial_adjoin_variables :
    Algebra.adjoin R (Set.range (powerRootPolynomialVariable R p hp)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using AddMonoidAlgebra.induction_on with
  | of q =>
      obtain ⟨n, k, h⟩ := powerRootPolynomial_single_exists R p hp q 1
      simp only [map_one, one_mul] at h
      change AddMonoidAlgebra.single q 1 ∈ _
      rw [h]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self n)) k
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy
  | smul a x hx => exact Subalgebra.smul_mem _ hx a

end SerrePositivity.BhattScholze.Andre
