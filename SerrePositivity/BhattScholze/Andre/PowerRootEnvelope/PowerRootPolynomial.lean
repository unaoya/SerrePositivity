module

public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionWitt

/-!
# 無限 p 冪根多項式環 A[Y^{1/p^∞}]

## 概要
指数の整数部分・小数部分への分解と評価、単項式基底、小数指数ごとの通常多項式座標と小数指数基底、δ 構造と完全 δ 構造、モニック商の自由性、mod p・係数主イデアル・係数イデアルの商との比較。
BS 著者版 Remark 7.15 の方程式商に使う無限 p 冪根多項式環を構成する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPD`、`PowerRootEnvelope/PowerRootInput`、`PowerRootEnvelope/Unconditional/Residue`、`PowerRootEnvelope/VarpiPD`、`Variants/MonicRootedExtension`。
-/

universe u v

/-! ## p 冪根多項式の指数と整数・小数部分の分解

## 概要

p 冪分母を持つ非負有理数の加法モノイドを具体的に構成し、
各指数を自然数部分と 1 未満の指数に一意に分解する。
BS 著者版 Remark 7.15（著者版 p.62）の無限 p 冪根変数の自由基底の準備。

## 方針

q pⁿ が自然数となる有理数を使う。加法は分母を pⁿ⁺ᵐ に揃えて閉じる。
有理数の床関数と小数部分を使い、同じ p 冪分母を保つことを剰余計算で示す。

## 規約

p の正値性だけを使い、素数性・係数環の標数は不要。
これは原典の pd 計算を補足する指数の具体的計算であり、prism の同定は含まない。

## 使われ方

単項式基底と、多項式環上の小数指数による自由基底に使う。
-/

@[expose] public noncomputable section PowerRootExponents

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：p 冪分母を持つ非負有理数の加法モノイド。
方針：分母を共通の p 冪にして加法の閉性を証明する。
規約：p は正とする。台集合には分母条件だけを書き、非負性は後で導く。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限 p 冪根単項式の指数。 -/
def powerRootExponentMonoid (p : ℕ) (_hp : 0 < p) : AddSubmonoid ℚ where
  carrier := {q | ∃ n a : ℕ, q * (p : ℚ) ^ n = a}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro q r ⟨n, a, hq⟩ ⟨m, b, hr⟩
    refine ⟨n + m, a * p ^ m + b * p ^ n, ?_⟩
    push_cast
    calc
      (q + r) * (p : ℚ) ^ (n + m) =
          (q * (p : ℚ) ^ n) * (p : ℚ) ^ m +
            (r * (p : ℚ) ^ m) * (p : ℚ) ^ n := by rw [pow_add]; ring
      _ = _ := by rw [hq, hr]

/-- 概要：自然数を p 冪根の指数とみなす。
方針：分母 1 の表示を使う。
規約：この写像は値として通常の自然数の有理数像を持つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常変数の整数冪。 -/
def powerRootNatExponent (p : ℕ) (hp : 0 < p) (n : ℕ) : powerRootExponentMonoid p hp :=
  ⟨n, 0, n, by simp⟩

/-- 概要：全ての p 冪根指数は非負。
方針：正の p 冪を掛けた値が自然数であることを使う。
規約：有理数としての順序で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の床関数による指数分解。 -/
theorem powerRootExponent_nonneg (p : ℕ) (hp : 0 < p) (q : powerRootExponentMonoid p hp) :
    0 ≤ (q : ℚ) := by
  obtain ⟨n, a, ha⟩ := q.property
  have hpos : 0 < (p : ℚ) ^ n := pow_pos (by exact_mod_cast hp) _
  exact (mul_nonneg_iff_of_pos_right hpos).mp (ha.symm ▸ Nat.cast_nonneg a)

/-- 概要：各指数は自然数を p 冪で割った形に書ける。
方針：定義の分母条件を、非零分母で割り戻す。
規約：非負の分子を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限段の単項式への帰着。 -/
theorem powerRootExponent_exists_repr (p : ℕ) (hp : 0 < p)
    (q : powerRootExponentMonoid p hp) :
    ∃ n a : ℕ, (q : ℚ) = a / (p : ℚ) ^ n := by
  obtain ⟨n, a, ha⟩ := q.property
  exact ⟨n, a, (eq_div_iff (pow_ne_zero _ (by exact_mod_cast hp.ne'))).mpr ha⟩

/-- 概要：1 未満の p 冪根指数の型。
方針：非負指数モノイドの部分型を取る。
規約：零指数も含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常多項式環上の基底の添字。 -/
abbrev PowerRootFraction (p : ℕ) (hp : 0 < p) :=
  {q : powerRootExponentMonoid p hp // (q : ℚ) < 1}

/-- 概要：小数部分を取っても指数の p 冪分母条件は保たれる。
方針：a/pⁿ の小数部分を (a mod pⁿ)/pⁿ と計算する。
規約：有理数の小数部分を同じ指数モノイドへ戻す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自由基底の整数部分との分離。 -/
def powerRootFractionalPart (p : ℕ) (hp : 0 < p) (q : powerRootExponentMonoid p hp) :
    PowerRootFraction p hp := by
  refine ⟨⟨Int.fract (q : ℚ), ?_⟩, Int.fract_lt_one _⟩
  obtain ⟨n, a, ha⟩ := powerRootExponent_exists_repr p hp q
  refine ⟨n, a % p ^ n, ?_⟩
  rw [ha, ← Nat.cast_pow, Int.fract_div_natCast_eq_div_natCast_mod]
  exact div_mul_cancel₀ _ (by positivity)

/-- 概要：各小数部分の有理数値は元の有理数の小数部分。
方針：具体的な構成の値を取り出す。
規約：分母の表示の選択には依存しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底添字同値の計算。 -/
theorem powerRootFractionalPart_val (p : ℕ) (hp : 0 < p) (q : powerRootExponentMonoid p hp) :
    ((powerRootFractionalPart p hp q).val : ℚ) = Int.fract (q : ℚ) := rfl

/-- 概要：各指数は自然数部分と 1 未満の指数に一意に分解する。
方針：床関数・小数部分と、それらの和による逆写像を使う。
規約：分解の逆は自然数指数と小数指数の加法そのもの。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限 p 冪根多項式環の自由基底。 -/
def powerRootExponentSplit (p : ℕ) (hp : 0 < p) :
    powerRootExponentMonoid p hp ≃ ℕ × PowerRootFraction p hp where
  toFun q := (⌊(q : ℚ)⌋₊, powerRootFractionalPart p hp q)
  invFun z := powerRootNatExponent p hp z.1 + z.2.val
  left_inv q := by
    apply Subtype.ext
    change (⌊(q : ℚ)⌋₊ : ℚ) + Int.fract (q : ℚ) = (q : ℚ)
    rw [natCast_floor_eq_intCast_floor (powerRootExponent_nonneg p hp q)]
    exact Int.floor_add_fract _
  right_inv z := by
    obtain ⟨n, a⟩ := z
    apply Prod.ext
    · change ⌊(n : ℚ) + (a.val : ℚ)⌋₊ = n
      rw [add_comm, Nat.floor_add_natCast (powerRootExponent_nonneg p hp a.val),
        Nat.floor_eq_zero.mpr a.property, zero_add]
    · apply Subtype.ext
      apply Subtype.ext
      change Int.fract ((n : ℚ) + (a.val : ℚ)) = (a.val : ℚ)
      rw [Int.fract_natCast_add]
      exact Int.fract_eq_self.mpr ⟨powerRootExponent_nonneg p hp a.val, a.property⟩

/-- 概要：p の n 乗根変数の指数は 1/pⁿ。
方針：正の p 冪による割算の恒等式で指数条件を示す。
規約：これは係数環の元ではなく有理数の指数である。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の互換な冪根変数。 -/
def powerRootVariableExponent (p : ℕ) (hp : 0 < p) (n : ℕ) :
    powerRootExponentMonoid p hp :=
  ⟨1 / (p : ℚ) ^ n, n, 1, div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hp.ne'))⟩

/-- 概要：隣接する冪根変数の指数を p 倍すると前の指数になる。
方針：正の p 冪を用いて有理数の等式を計算する。
規約：モノイド上の p 倍は加法的な自然数作用。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Yₙ₊₁ᵖ=Yₙ。 -/
theorem powerRootVariableExponent_nsmul (p : ℕ) (hp : 0 < p) (n : ℕ) :
    p • powerRootVariableExponent p hp (n + 1) = powerRootVariableExponent p hp n := by
  apply Subtype.ext
  change p • (1 / (p : ℚ) ^ (n + 1)) = 1 / (p : ℚ) ^ n
  rw [nsmul_eq_mul, pow_succ']
  field_simp

/-- 概要：全指数は一つの冪根変数の自然数倍として表される。
方針：p 冪分母の表示を自然数作用へ書き直す。
規約：段 n と冪 k は指数に依存して選べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限変数環を有限段から生成する。 -/
theorem powerRootExponent_exists_nsmul (p : ℕ) (hp : 0 < p)
    (q : powerRootExponentMonoid p hp) :
    ∃ n k : ℕ, q = k • powerRootVariableExponent p hp n := by
  obtain ⟨n, k, hq⟩ := powerRootExponent_exists_repr p hp q
  refine ⟨n, k, ?_⟩
  apply Subtype.ext
  change (q : ℚ) = k • (1 / (p : ℚ) ^ n)
  rw [nsmul_eq_mul, hq, div_eq_mul_inv, one_div]

/-- 概要：自然数指数を足すと整数部分だけが同じ自然数だけ増える。
方針：床関数と小数部分の自然数平行移動公式を使う。
規約：小数部分の添字は変わらない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常変数の作用と小数指数基底の整合性。 -/
theorem powerRootExponentSplit_nat_add (p : ℕ) (hp : 0 < p)
    (n : ℕ) (q : powerRootExponentMonoid p hp) :
    powerRootExponentSplit p hp (powerRootNatExponent p hp n + q) =
      (n + (powerRootExponentSplit p hp q).1, (powerRootExponentSplit p hp q).2) := by
  apply Prod.ext
  · change ⌊(n : ℚ) + (q : ℚ)⌋₊ = n + ⌊(q : ℚ)⌋₊
    rw [add_comm, Nat.floor_add_natCast (powerRootExponent_nonneg p hp q), Nat.add_comm]
  · apply Subtype.ext
    apply Subtype.ext
    change Int.fract ((n : ℚ) + (q : ℚ)) = Int.fract (q : ℚ)
    exact Int.fract_natCast_add _ _

end SerrePositivity.BhattScholze.Andre

end PowerRootExponents

/-! ## 無限 p 冪根多項式環の単項式基底

## 概要

p 冪分母を持つ非負有理数を指数とする加法モノイド環を構成する。
これは互換な変数 Yₙ、Yₙ₊₁ᵖ=Yₙ を持ち、全単項式は一つの有限段の変数の冪となる。
係数環上の具体的単項式基底を備える。
BS 著者版 Remark 7.15（著者版 p.62）の R/ϖ[Y¹⸍ᵖ∞] の自由性の計算。

## 方針

指数の p 冪分母表示と既存の加法モノイド環の単項式基底を使う。
小数指数による通常多項式環上の分解と、モニック冪商への移送の準備である。

## 規約

係数環の標数・非零性・被約性は仮定しない。p の正値性だけを使う。
p 進完備化した環を定義するものではない。

## 使われ方

原典の pd 計算における未完備の無限 p 冪根多項式環の自由性を供給する。
-/

@[expose] public noncomputable section PowerRootPolynomial

namespace SerrePositivity.BhattScholze.Andre
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)

/-- 概要：無限 p 冪根の一変数多項式環の具体的な単項式表示。
方針：非負 p 冪分母指数の加法モノイド環を使う。
規約：各元は有限個の指数だけを持つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の未完備環 P。 -/
abbrev PowerRootPolynomial := AddMonoidAlgebra R (powerRootExponentMonoid p hp)

/-- 概要：互換な p 冪根変数 Yₙ。
方針：指数 1/pⁿ、係数 1 の単項式を取る。
規約：Y₀ が通常の変数に当たる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限段の包含。 -/
def powerRootPolynomialVariable (n : ℕ) : PowerRootPolynomial R p hp :=
  AddMonoidAlgebra.single (powerRootVariableExponent p hp n) 1

/-- 概要：構成した変数は Yₙ₊₁ᵖ=Yₙ を満たす。
方針：単項式の冪の公式と指数の p 倍の等式を使う。
規約：係数環に関する仮定は追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限 p 冪根の関係式。 -/
theorem powerRootPolynomialVariable_pow (n : ℕ) :
    powerRootPolynomialVariable R p hp (n + 1) ^ p = powerRootPolynomialVariable R p hp n := by
  simp only [powerRootPolynomialVariable, AddMonoidAlgebra.single_pow,
    powerRootVariableExponent_nsmul, one_pow]

/-- 概要：全ての単項式はある有限段の変数の冪と係数の積に書ける。
方針：指数の p 冪分母表示と単項式の冪の公式を使う。
規約：段は単項式ごとに選び、係数環の非零性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有限段からの生成。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の P の自由性。 -/
def powerRootPolynomialBasis :
    Module.Basis (powerRootExponentMonoid p hp) R (PowerRootPolynomial R p hp) :=
  AddMonoidAlgebra.basis _ R

/-- 概要：構成した基底の各値は指数 q、係数 1 の単項式。
方針：標準加法モノイド環基底の値を取り出す。
規約：具体的な単項式表示を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の自由基底の計算。 -/
theorem powerRootPolynomialBasis_apply (q : powerRootExponentMonoid p hp) :
    powerRootPolynomialBasis R p hp q = AddMonoidAlgebra.single q 1 := rfl

/-- 概要：無限 p 冪根多項式環は元の係数環上自由。
方針：具体的単項式基底から自由性を得る。
規約：係数環の標数や p ねじれなしは要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の通常代数計算。 -/
theorem powerRootPolynomial_free : Module.Free R (PowerRootPolynomial R p hp) :=
  Module.Free.of_basis (powerRootPolynomialBasis R p hp)

/-- 概要：互換な p 冪根変数の全体はこの環を係数環上生成する。
方針：各単項式をある段の変数の冪に書き、単項式の線形生成を使う。
規約：有限個の変数だけを固定して生成すると主張するものではない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限 p 冪根変数環の具体的表示。 -/
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

end PowerRootPolynomial

/-! ## 無限 p 冪根多項式環の δ 構造

## 概要

p 正則な δ 係数環上で、無限 p 冪根多項式環に全根変数が rank 1 となる δ 構造を与える。
BS 著者版 Remark 7.15（著者版 p.62）の無限根変数への実 pd 計算の準備。

## 方針

単項式の指数を p 倍し係数に元の Frobenius を作用させる環射を構成する。
mod p で通常の p 乗と一致することを加法モノイド環の帰納法で証明し、
p 正則環の Frobenius 持ち上げから δ 構造を得る。

## 規約

係数環の p 正則性を明示する。元の無限根多項式環の台環を変更しない。
p 進完備化や prismatic envelope との同定はこのファイルに含まない。

## 使われ方

無限 p 冪根多項式環上のモニック入力に実 mod p 分冪包の構成を適用する。
-/

@[expose] public noncomputable section PowerRootPolynomialDelta

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp

/-- 概要：無限根指数の p 倍を取る加法モノイド射。
方針：自然数倍の加法保存性を使う。
規約：指数は同じ p 冪分母の非負有理数型に属する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の単項式 Frobenius。 -/
def powerRootExponentPrimeScale : G →+ G where
  toFun q := p • q
  map_zero' := nsmul_zero p
  map_add' x y := nsmul_add x y p

/-- 概要：係数 Frobenius と指数 p 倍による無限根多項式環の環自己射。
方針：モノイド環の係数写像と指数写像を合成する。
規約：通常の p 乗写像とは mod p で比較する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 構造の Frobenius 持ち上げ。 -/
def powerRootPolynomialFrobenius (D : DeltaStructure p A) : P →+* P :=
  (AddMonoidAlgebra.mapDomainRingHom A (powerRootExponentPrimeScale p)).comp
    (AddMonoidAlgebra.mapRingHom G D.frobeniusLift)

/-- 概要：単項式の Frobenius は係数 Frobenius と指数 p 倍を取る。
方針：係数写像と指数写像の単項式公式を使う。
規約：任意の係数と指数について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根変数の rank 1 性。 -/
theorem powerRootPolynomialFrobenius_single (D : DeltaStructure p A) (q : G) (a : A) :
    powerRootPolynomialFrobenius p D (AddMonoidAlgebra.single q a) =
      AddMonoidAlgebra.single (p • q) (D.frobeniusLift a) := by
  change AddMonoidAlgebra.mapDomain (powerRootExponentPrimeScale p)
    (AddMonoidAlgebra.mapRingHom G D.frobeniusLift (AddMonoidAlgebra.single q a)) = _
  rw [AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomain_single]
  rfl

/-- 概要：無限根多項式の Frobenius は係数上で元の Frobenius を延長する。
方針：零指数の単項式として係数を計算する。
規約：元の標準係数射を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底 δ 構造との整合性。 -/
theorem powerRootPolynomialFrobenius_coeff (D : DeltaStructure p A) (a : A) :
    powerRootPolynomialFrobenius p D (algebraMap A P a) = algebraMap A P (D.frobeniusLift a) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootPolynomialFrobenius_single p D (0 : G) a

/-- 概要：係数環の p 正則性は無限根多項式環へ移る。
方針：単項式基底による自由性と平坦性を使う。
規約：係数環の非零性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 構造の存在への入力。 -/
theorem powerRootPolynomial_primeRegular
    (hpA : Function.Injective (fun a : A => (p : A) * a)) :
    Function.Injective (fun a : P => (p : P) * a) := by
  let := powerRootPolynomial_free A p hp
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)

/-- 概要：構成した Frobenius は実 mod p 商で通常の p 乗に一致する。
方針：単項式・加法・係数倍の帰納法と、素数 p の二項係数公式を使う。
規約：零係数環も含め、CharP インスタンスを要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 持ち上げからの δ 構造。 -/
theorem powerRootPolynomialFrobenius_mod_prime (D : DeltaStructure p A) (x : P) :
    Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootPolynomialFrobenius p D x) =
      Ideal.Quotient.mk (Ideal.span {(p : P)}) x ^ p := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : P)})
  have hpQ : (p : P ⧸ Ideal.span {(p : P)}) = 0 := by
    change q (p : P) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hcoeff (a : A) : q (powerRootPolynomialFrobenius p D (algebraMap A P a)) =
      q (algebraMap A P a) ^ p := by
    rw [powerRootPolynomialFrobenius_coeff, D.frobeniusLift_apply]
    simp only [map_add, map_mul, map_natCast, map_pow, hpQ, zero_mul, add_zero]
  change q (powerRootPolynomialFrobenius p D x) = q x ^ p
  induction x using AddMonoidAlgebra.induction_on with
  | of t =>
    change q (powerRootPolynomialFrobenius p D (AddMonoidAlgebra.single t 1)) =
      q (AddMonoidAlgebra.single t 1) ^ p
    rw [powerRootPolynomialFrobenius_single, map_one, ← map_pow,
      AddMonoidAlgebra.single_pow, one_pow]
  | add x z hx hz =>
    simp only [map_add, hx, hz]
    symm
    simpa only [hpQ, zero_mul, add_zero] using
      add_pow_prime_eq' (Fact.out : p.Prime) (q x) (q z)
  | smul a x hx =>
    rw [Algebra.smul_def]
    simp only [map_mul, hcoeff, hx, mul_pow]

/-- 概要：p 正則な係数環上では指定した無限根 Frobenius を持つ δ 構造が一意に存在する。
方針：自由性による p 正則性と実 mod p 一致を Frobenius 持ち上げの存在定理へ渡す。
規約：元の無限根多項式環の上で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根変数の実 δ 持ち上げ。 -/
theorem existsUnique_powerRootPolynomialDelta
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    ∃! E : DeltaStructure p P, E.frobeniusLift = powerRootPolynomialFrobenius p D :=
  DeltaStructure.existsUnique_of_mod_p (powerRootPolynomial_primeRegular p hpA)
    (powerRootPolynomialFrobenius p D) (powerRootPolynomialFrobenius_mod_prime p D)

/-- 概要：係数 Frobenius と全無限根変数の rank 1 性を指定した δ 構造。
方針：一意存在した構造を選ぶ。
規約：p 正則性を明示し、ねじれを持つ係数環へ無条件に延長しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根多項式入力の分冪包。 -/
def powerRootPolynomialDelta
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    DeltaStructure p P :=
  Classical.choose (existsUnique_powerRootPolynomialDelta p hpA D)

/-- 概要：選んだ δ 構造の Frobenius は指定した単項式 Frobenius に一致する。
方針：一意存在の存在証人の性質を取り出す。
規約：元の係数環の Frobenius を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数と変数上の δ の計算。 -/
theorem powerRootPolynomialDelta_frobenius
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    (powerRootPolynomialDelta p hpA D).frobeniusLift = powerRootPolynomialFrobenius p D :=
  (Classical.choose_spec (existsUnique_powerRootPolynomialDelta p hpA D)).1


/-- 概要：各無限根変数の Frobenius はその p 乗。
方針：係数 1 の単項式上の指数 p 倍公式を使う。
規約：全ての段 n で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全根変数の rank 1 性。 -/
theorem powerRootPolynomialFrobenius_variable (D : DeltaStructure p A) (n : ℕ) :
    powerRootPolynomialFrobenius p D (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable A p hp n ^ p := by
  change powerRootPolynomialFrobenius p D (AddMonoidAlgebra.single _ 1) =
    AddMonoidAlgebra.single _ 1 ^ p
  rw [powerRootPolynomialFrobenius_single, map_one, AddMonoidAlgebra.single_pow, one_pow]

/-- 概要：無限根多項式環への標準係数射は実 δ 射である。
方針：係数 Frobenius の互換性と終域の p 正則性から δ の互換性を得る。
規約：元の係数環の δ 構造を延長する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数側との整合性。 -/
theorem powerRootPolynomialDelta_coeff_isDeltaHom
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) :
    D.IsDeltaHom (powerRootPolynomialDelta p hpA D) (algebraMap A P) := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift (algebraMap A P)
    (powerRootPolynomial_primeRegular p hpA)
  intro a
  rw [powerRootPolynomialDelta_frobenius, powerRootPolynomialFrobenius_coeff]

/-- 概要：全無限根変数の δ は零。
方針：Frobenius が p 乗になる公式と δ の恒等式を比較し、p 正則性で消去する。
規約：任意の段 n を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根変数の実 rank 1 δ 持ち上げ。 -/
theorem powerRootPolynomialDelta_variable
    (hpA : Function.Injective (fun a : A => (p : A) * a)) (D : DeltaStructure p A) (n : ℕ) :
    (powerRootPolynomialDelta p hpA D).delta (powerRootPolynomialVariable A p hp n) = 0 := by
  apply powerRootPolynomial_primeRegular p hpA
  have he : (powerRootPolynomialDelta p hpA D).frobeniusLift
      (powerRootPolynomialVariable A p hp n) = powerRootPolynomialVariable A p hp n ^ p := by
    rw [powerRootPolynomialDelta_frobenius, powerRootPolynomialFrobenius_variable]
  have hδ := (powerRootPolynomialDelta p hpA D).frobeniusLift_apply
    (powerRootPolynomialVariable A p hp n)
  linear_combination he - hδ

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialDelta

/-! ## 小数指数ごとの通常多項式座標

## 概要

無限 p 冪根多項式環の元を、1 未満の小数指数で添字付けた有限個の通常多項式へ分解する。
BS 著者版 Remark 7.15（著者版 p.62）のモニック冪商の自由基底の準備。

## 方針

単項式の指数を自然数部分と小数部分に分け、係数の有限台関数を curry する。
通常変数 Y₀ の多項式評価射も明示する。

## 規約

ここでは元の係数環上の線形同型を構成する。通常多項式環上の線形性は次工程で示す。
係数環の標数や非零性は不要。p は正とする。

## 使われ方

小数指数による通常多項式環上の自由基底とモニック冪商への移送に使う。
-/

@[expose] public noncomputable section PowerRootPolynomialCoordinates

namespace SerrePositivity.BhattScholze.Andre
open Polynomial
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial R p hp
local notation "G" => powerRootExponentMonoid p hp
local notation "F" => PowerRootFraction p hp

/-- 概要：通常変数を Y₀ に送る、通常多項式環からの係数射。
方針：標準多項式評価代数射を使う。
規約：係数環 R の作用は元の加法モノイド環の作用を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の P/(fᵖ) の f の像。 -/
def powerRootPolynomialBaseMap : R[X] →ₐ[R] P :=
  Polynomial.aeval (powerRootPolynomialVariable R p hp 0)

/-- 概要：標準多項式評価射による通常多項式環上の代数構造。
方針：明示した係数射の toAlgebra を使う。
規約：他の多項式代数作用と混同しないよう局所導入する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の小数指数基底。 -/
@[instance_reducible] def powerRootPolynomialBaseAlgebra : Algebra R[X] P :=
  (powerRootPolynomialBaseMap R p hp).toRingHom.toAlgebra

/-- 概要：単項式は自然数部分ごとの通常多項式を小数指数で有限個並べる座標を持つ。
方針：指数の分解による添字の同値、curry、通常多項式の係数表示を合成する。
規約：この段階では元の R 上の線形同型。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の明示的自由基底。 -/
def powerRootPolynomialCoordinates : P ≃ₗ[R] (F →₀ R[X]) := by
  let eP : R[X] ≃ₗ[R] (ℕ →₀ R) :=
    (Polynomial.toFinsuppIsoLinear R).trans (AddMonoidAlgebra.coeffLinearEquiv R)
  let eG := (powerRootExponentSplit p hp).trans (Equiv.prodComm ℕ F)
  exact (AddMonoidAlgebra.coeffLinearEquiv R).trans
    ((Finsupp.domLCongr eG).trans
      ((Finsupp.curryLinearEquiv R).trans (Finsupp.mapRange.linearEquiv eP.symm)))

/-- 概要：単項式の座標は、小数部分の成分の自然数部分の単項式となる。
方針：添字変更・curry・多項式係数表示を一項の有限台関数上で計算する。
規約：係数 a はそのまま保たれる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常変数作用との整合性。 -/
theorem powerRootPolynomialCoordinates_single (q : G) (a : R) :
    powerRootPolynomialCoordinates R p hp (AddMonoidAlgebra.single q a) =
      Finsupp.single (powerRootExponentSplit p hp q).2
        (Polynomial.monomial (powerRootExponentSplit p hp q).1 a) := by
  simp [powerRootPolynomialCoordinates, Finsupp.curry_single]
  rfl

/-- 概要：通常多項式の単項式は自然数指数の単項式に写る。
方針：Y₀ の指数が 1 であることと、単項式の冪の公式を使う。
規約：この公式は標準多項式係数射について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常変数の作用の照合。 -/
theorem powerRootPolynomialBaseMap_monomial (n : ℕ) (a : R) :
    powerRootPolynomialBaseMap R p hp (Polynomial.monomial n a) =
      AddMonoidAlgebra.single (powerRootNatExponent p hp n) a := by
  have he : n • powerRootVariableExponent p hp 0 = powerRootNatExponent p hp n := by
    apply Subtype.ext
    change n • (1 / (p : ℚ) ^ 0) = (n : ℚ)
    simp
  simp [powerRootPolynomialBaseMap, Polynomial.aeval_monomial,
    powerRootPolynomialVariable, AddMonoidAlgebra.single_pow, he]

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialCoordinates

/-! ## 通常多項式環上の小数指数基底

## 概要

無限 p 冪根多項式環は、通常変数を Y₀ に送る多項式環上で自由であり、
1 未満の p 冪分母指数の単項式が基底となる。
BS 著者版 Remark 7.15（著者版 p.62）のモニック冪商の自由性の入力。

## 方針

小数指数ごとの座標同型が通常多項式環上線形であることを、単項式の積で確かめる。
整数指数の加法が小数部分を保つ公式を使う。

## 規約

p は正とする。係数環の標数・非零性は不要。
標準評価射の toAlgebra に関する自由性を述べる。

## 使われ方

モニック冪商へ基底変更して、元の係数環上の自由基底を構成する。
-/

@[expose] public noncomputable section PowerRootPolynomialFractionBasis

namespace SerrePositivity.BhattScholze.Andre
open Polynomial
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial R p hp
local notation "G" => powerRootExponentMonoid p hp
local notation "F" => PowerRootFraction p hp
local notation "E" => powerRootPolynomialCoordinates R p hp

/-- 概要：小数指数ごとの座標は通常多項式環のスカラー作用を保つ。
方針：多項式と有限台係数を単項式へ分解し、指数の整数平行移動を計算する。
規約：作用は Y₀ への標準多項式評価射による。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常多項式環上の自由基底。 -/
theorem powerRootPolynomialCoordinates_smul :
    letI := powerRootPolynomialBaseAlgebra R p hp
    ∀ (f : R[X]) (x : P), E (f • x) = f • E x := by
  let := powerRootPolynomialBaseAlgebra R p hp
  intro f x
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [add_smul, map_add, hf, hg, add_smul]
  | monomial n a =>
      let e0 : P ≃ₗ[R] (G →₀ R) := AddMonoidAlgebra.coeffLinearEquiv R
      obtain ⟨v, rfl⟩ := e0.symm.surjective x
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw =>
          change E ((Polynomial.monomial n a) • AddMonoidAlgebra.ofCoeff v) =
            (Polynomial.monomial n a) • E (AddMonoidAlgebra.ofCoeff v) at hv
          change E ((Polynomial.monomial n a) • AddMonoidAlgebra.ofCoeff w) =
            (Polynomial.monomial n a) • E (AddMonoidAlgebra.ofCoeff w) at hw
          change E ((Polynomial.monomial n a) •
              (AddMonoidAlgebra.ofCoeff v + AddMonoidAlgebra.ofCoeff w)) =
            (Polynomial.monomial n a) • E
              (AddMonoidAlgebra.ofCoeff v + AddMonoidAlgebra.ofCoeff w)
          rw [smul_add, map_add, hv, hw, map_add, smul_add]
      | single q b =>
          change E ((powerRootPolynomialBaseMap R p hp (Polynomial.monomial n a)) *
              AddMonoidAlgebra.single q b) =
            (Polynomial.monomial n a) • E (AddMonoidAlgebra.single q b)
          rw [powerRootPolynomialBaseMap_monomial, AddMonoidAlgebra.single_mul_single,
            powerRootPolynomialCoordinates_single, powerRootPolynomialCoordinates_single,
            powerRootExponentSplit_nat_add]
          simp [Finsupp.smul_single, smul_eq_mul, Polynomial.monomial_mul_monomial]

/-- 概要：小数指数座標の同型は、通常多項式環上の線形同型でもある。
方針：元の加法同型に検証済みのスカラー作用の保存を付ける。
規約：標準評価射の toAlgebra を局所導入する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック商への基底変更。 -/
def powerRootPolynomialCoordinatesPolynomialLinearEquiv :
    letI := powerRootPolynomialBaseAlgebra R p hp
    P ≃ₗ[R[X]] (F →₀ R[X]) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact { (E).toAddEquiv with map_smul' := powerRootPolynomialCoordinates_smul R p hp }

/-- 概要：1 未満の指数の単項式が通常多項式環上の基底を与える。
方針：通常多項式環上の座標同型を基底の repr とする。
規約：係数環の非零性や標数を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の P/(fᵖ) の自由性。 -/
def powerRootPolynomialFractionBasis :
    letI := powerRootPolynomialBaseAlgebra R p hp
    Module.Basis F R[X] P := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact Module.Basis.ofRepr (powerRootPolynomialCoordinatesPolynomialLinearEquiv R p hp)

/-- 概要：小数指数基底の値はその指数の係数 1 の単項式そのもの。
方針：座標同型で両辺を比較し、小数指数の床が零であることを使う。
規約：基底の存在だけでなく具体的な値を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の明示的自由基底。 -/
theorem powerRootPolynomialFractionBasis_apply (a : F) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    powerRootPolynomialFractionBasis R p hp a = AddMonoidAlgebra.single a.val 1 := by
  let := powerRootPolynomialBaseAlgebra R p hp
  have hs : powerRootExponentSplit p hp a.val = (0, a) := by
    apply Prod.ext
    · exact Nat.floor_eq_zero.mpr a.property
    · apply Subtype.ext
      apply Subtype.ext
      exact Int.fract_eq_self.mpr ⟨powerRootExponent_nonneg p hp a.val, a.property⟩
  apply (E).injective
  change E ((E).symm (Finsupp.single a 1)) = E (AddMonoidAlgebra.single a.val 1)
  rw [LinearEquiv.apply_symm_apply, powerRootPolynomialCoordinates_single, hs]
  simp

/-- 概要：無限 p 冪根多項式環は標準通常多項式環上自由。
方針：具体的な小数指数基底から自由性を得る。
規約：作用は通常変数を Y₀ に送る射による。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック冪商と係数環上の自由性。 -/
theorem powerRootPolynomial_free_over_polynomial :
    letI := powerRootPolynomialBaseAlgebra R p hp
    Module.Free R[X] P := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact Module.Free.of_basis (powerRootPolynomialFractionBasis R p hp)

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialFractionBasis

/-! ## 無限 p 冪根多項式環内のモニック商の自由性

## 概要

無限 p 冪根多項式環内で通常多項式 f の像を零とする商は、f がモニックなら
元の係数環上自由であり、正次数なら忠実平坦でもある。
BS 著者版 Remark 7.15（著者版 p.62）の P/(fᵖ) の自由性の計算。

## 方針

通常多項式環上の小数指数基底を、通常モニック商へ基底変更する。
商とテンソルの標準同型を使い、通常モニック剰余の冪基底と合成する。

## 規約

係数環の標数・非零性は要求しない。自由性には正次数は不要。
prismatic envelope の Frobenius 引戻しとの同定は含まない。

## 使われ方

fᵖ に適用して、原典の具体的 pd 包の係数環の自由性と忠実平坦性を供給する。
-/

@[expose] public noncomputable section PowerRootMonicQuotient

namespace SerrePositivity.BhattScholze.Andre
open Polynomial
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial R p hp
local notation "F" => PowerRootFraction p hp

/-- 概要：通常多項式環を経由する係数作用は元の係数環の作用と整合する。
方針：標準評価代数射が係数を保つことを使う。
規約：元の加法モノイド環の R 作用を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の商の自由性のスカラー塔。 -/
theorem powerRootPolynomialBase_isScalarTower :
    letI := powerRootPolynomialBaseAlgebra R p hp
    IsScalarTower R R[X] P := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact IsScalarTower.of_algebraMap_eq' (powerRootPolynomialBaseMap R p hp).comp_algebraMap.symm

/-- 概要：通常多項式 f の像を零とする無限 p 冪根多項式環の商。
方針：標準多項式係数射で拡張した主イデアルで割る。
規約：係数環 R の作用を商に誘導する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の P/(fᵖ)。 -/
abbrev PowerRootPolynomialQuotient (f : R[X]) :=
  letI := powerRootPolynomialBaseAlgebra R p hp
  P ⧸ (Ideal.span {f}).map (algebraMap R[X] P)

/-- 概要：商を定める拡張イデアルは f の標準評価像の主イデアル。
方針：イデアルの span の像の公式を使う。
規約：通常変数は Y₀ に送る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典のモニック関係との照合。 -/
theorem powerRootPolynomialQuotient_ideal (f : R[X]) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    (Ideal.span {f}).map (algebraMap R[X] P) =
      Ideal.span {powerRootPolynomialBaseMap R p hp f} := by
  let := powerRootPolynomialBaseAlgebra R p hp
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- 概要：通常モニック商を経由する作用は元の係数環上の商作用と整合する。
方針：係数 r の両方の像を実商代表元で比較し、標準評価射の係数保存を使う。
規約：f のモニック性はこの作用の整合性には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの基底の合成。 -/
theorem powerRootPolynomialQuotient_isScalarTower (f : R[X]) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    IsScalarTower R (R[X] ⧸ Ideal.span {f}) (PowerRootPolynomialQuotient R p hp f) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change Ideal.Quotient.mk _ (algebraMap R P r) =
    Ideal.Quotient.mk _ (powerRootPolynomialBaseMap R p hp (Polynomial.C r))
  exact congrArg (Ideal.Quotient.mk _) ((powerRootPolynomialBaseMap R p hp).commutes r).symm

/-- 概要：無限 p 冪根モニック商は、通常モニック商上で小数指数を基底に持つ。
方針：小数指数基底を商環へ基底変更し、実商とテンソルの標準同型で戻す。
規約：この商環上の基底自体には f のモニック性を必要としない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数環上の自由基底。 -/
def powerRootPolynomialQuotientFractionBasis (f : R[X]) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    Module.Basis F (R[X] ⧸ Ideal.span {f}) (PowerRootPolynomialQuotient R p hp f) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact ((powerRootPolynomialFractionBasis R p hp).baseChange (R[X] ⧸ Ideal.span {f})).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor P (Ideal.span {f})).symm.toLinearEquiv

/-- 概要：モニック商は小数指数と通常剰余の冪を組み合わせた基底を持つ。
方針：通常モニック商の冪基底と、小数指数の基底変更をスカラー塔で合成する。
規約：正次数や係数環の非零性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の P/(fᵖ) の自由基底。 -/
def powerRootPolynomialQuotientBasis (f : R[X]) (hf : f.Monic) :
    Module.Basis (Fin f.natDegree × F) R (PowerRootPolynomialQuotient R p hp f) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  let := powerRootPolynomialBase_isScalarTower R p hp
  let := powerRootPolynomialQuotient_isScalarTower R p hp f
  let bR : Module.Basis (Fin f.natDegree) R (R[X] ⧸ Ideal.span {f}) :=
    AdjoinRoot.powerBasisAux' hf
  exact bR.smulTower (powerRootPolynomialQuotientFractionBasis R p hp f)

/-- 概要：無限 p 冪根多項式環のモニック商は元の係数環上自由。
方針：具体的なモニック商基底から自由性を得る。
規約：自由性には正次数を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック冪商。 -/
theorem powerRootPolynomialQuotient_free (f : R[X]) (hf : f.Monic) :
    Module.Free R (PowerRootPolynomialQuotient R p hp f) :=
  Module.Free.of_basis (powerRootPolynomialQuotientBasis R p hp f hf)

/-- 概要：正次数モニックの無限 p 冪根多項式商は元の係数環上忠実平坦。
方針：零係数環を分け、非零枝では非空の具体的基底から非零性と自由忠実平坦性を得る。
規約：モニック定数 1 を除外するため正次数を要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包への係数拡大。 -/
theorem powerRootPolynomialQuotient_faithfullyFlat (f : R[X]) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R (PowerRootPolynomialQuotient R p hp f) := by
  let := powerRootPolynomialQuotient_free R p hp f hf
  rcases subsingleton_or_nontrivial R with hs | hn
  · let := hs
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hn
    let a0 : F := ⟨0, by norm_num⟩
    let : Nonempty (Fin f.natDegree × F) := ⟨(⟨0, hdeg⟩, a0)⟩
    let b := powerRootPolynomialQuotientBasis R p hp f hf
    let : Nontrivial (PowerRootPolynomialQuotient R p hp f) := b.repr.symm.injective.nontrivial
    infer_instance

/-- 概要：無限 p 冪根多項式環におけるモニック多項式の像は非零因子。
方針：通常多項式環上のモニック元の正則性を、小数指数基底による平坦性で移す。
規約：零係数環も許し、正次数は要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正則元の pd 包の計算。 -/
theorem powerRootPolynomial_monic_regular (f : R[X]) (hf : f.Monic) :
    IsSMulRegular P (powerRootPolynomialBaseMap R p hp f) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  let := powerRootPolynomial_free_over_polynomial R p hp
  have hr : IsSMulRegular R[X] f := hf.isRegular.left
  exact hr.of_flat (S := P)

/-- 概要：モニック f の p 乗を課した無限 p 冪根多項式商は係数環上自由。
方針：モニック性が冪で保たれることを一般のモニック商の基底に適用する。
規約：係数環の標数や f の正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の P/(fᵖ) の自由性。 -/
theorem powerRootPolynomialPowerQuotient_free (f : R[X]) (hf : f.Monic) :
    Module.Free R (PowerRootPolynomialQuotient R p hp (f ^ p)) :=
  powerRootPolynomialQuotient_free R p hp (f ^ p) (hf.pow p)

/-- 概要：正次数モニック f の p 乗商は元の係数環上忠実平坦。
方針：モニック性と正次数の冪に関する公式を一般商の忠実平坦性へ渡す。
規約：p の素数性・係数環の標数は不要で、p の正値性だけを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 包の係数環。 -/
theorem powerRootPolynomialPowerQuotient_faithfullyFlat (f : R[X]) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R (PowerRootPolynomialQuotient R p hp (f ^ p)) := by
  apply powerRootPolynomialQuotient_faithfullyFlat R p hp (f ^ p) (hf.pow p)
  rw [hf.natDegree_pow]
  exact Nat.mul_pos hp hdeg

end SerrePositivity.BhattScholze.Andre

end PowerRootMonicQuotient

/-! ## 無限 p 冪根多項式環の実 mod p 係数比較

## 概要

無限 p 冪根多項式環を p で割ることと、係数環を p で割って同じ指数モノイド環を
作ることは可換である。BS 著者版 Remark 7.15（著者版 p.62）の無限根変数上の正則性の入力。

## 方針

係数商射から誘導される環射の全射性と、核が p 主イデアルであることを係数ごとに証明する。
第一同型定理を用いて実商同士の同型を構成する。

## 規約

p は正の自然数。素数性、係数環の標数・非零性・p 正則性は不要。
同じ実指数モノイドと標準係数射を保持する。

## 使われ方

mod p のモニック多項式を係数商上でモニックとして扱い、無限根環での正則性を得る。
-/

@[expose] public noncomputable section PowerRootPolynomialModPrime

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "R" => A ⧸ Ideal.span {(p : A)}
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 概要：無限根多項式の各係数を mod p に送る標準環射。
方針：加法モノイド環の係数環射を使う。
規約：指数と全根変数の番号は変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数商比較。 -/
def powerRootPolynomialModPrimeMap : P →+* Pbar :=
  AddMonoidAlgebra.mapRingHom G bar

/-- 概要：係数商射は各単項式の係数だけを mod p に送る。
方針：モノイド環の係数写像の単項式公式を使う。
規約：任意の係数・指数について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の変数と係数の照合。 -/
theorem powerRootPolynomialModPrimeMap_single (q : G) (a : A) :
    powerRootPolynomialModPrimeMap A p hp (AddMonoidAlgebra.single q a) =
      AddMonoidAlgebra.single q (bar a) :=
  AddMonoidAlgebra.mapRingHom_single _ _ _

/-- 概要：係数商射は標準係数射と可換。
方針：係数を零指数の単項式として計算する。
規約：同じ元の係数環 A からの作用を比較する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常多項式評価の自然性。 -/
theorem powerRootPolynomialModPrimeMap_coeff (a : A) :
    powerRootPolynomialModPrimeMap A p hp (algebraMap A P a) = algebraMap R Pbar (bar a) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using powerRootPolynomialModPrimeMap_single A p hp 0 a

/-- 概要：無限根多項式の係数商射は全射。
方針：元の係数商射の全射性をモノイド環へ移す。
規約：有限支持を保って係数を持ち上げる既存の構成を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実商比較同型の存在。 -/
theorem powerRootPolynomialModPrimeMap_surjective :
    Function.Surjective (powerRootPolynomialModPrimeMap A p hp) :=
  AddMonoidAlgebra.map_surjective (bar).toAddMonoidHom Ideal.Quotient.mk_surjective

/-- 概要：無限根多項式の係数商射の核は同じ環内の p 主イデアル。
方針：核の元の全係数が p で割れることを使い、各単項式を p の倍数として足し戻す。
規約：係数環の非零性や p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 mod p 商の同定。 -/
theorem powerRootPolynomialModPrimeMap_ker :
    RingHom.ker (powerRootPolynomialModPrimeMap A p hp) = Ideal.span {(p : P)} := by
  classical
  apply le_antisymm
  · intro x hx
    have hzero : powerRootPolynomialModPrimeMap A p hp x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply (Ideal.span {(p : P)}).sum_mem
    intro q _
    have hcoeff : bar (x.coeff q) = 0 := by
      have h := congrArg (fun z : Pbar => z.coeff q) hzero
      simpa only [powerRootPolynomialModPrimeMap, AddMonoidAlgebra.coeff_mapRingHom,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)
    rw [hb]
    have he : AddMonoidAlgebra.single q ((p : A) * b) =
        (p : P) * AddMonoidAlgebra.single q b := by
      rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single, zero_add]
    rw [he]
    exact (Ideal.span {(p : P)}).mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = _)
    change powerRootPolynomialModPrimeMap A p hp (p : P) = 0
    rw [map_natCast]
    have hpR : (p : R) = 0 := by
      change bar (p : A) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R Pbar) hpR

/-- 概要：実無限根環の mod p 商は係数商上の同じ無限根環と環同型。
方針：係数商射の核の同定と全射性に第一同型定理を適用する。
規約：同じ指数型を用い、完備化は行わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック入力の mod p 正則性の移送。 -/
def powerRootPolynomialModPrimeEquiv :
    (P ⧸ Ideal.span {(p : P)}) ≃+* Pbar :=
  (Ideal.quotEquivOfEq (powerRootPolynomialModPrimeMap_ker A p hp).symm).trans
    ((powerRootPolynomialModPrimeMap A p hp).quotientKerEquivOfSurjective
      (powerRootPolynomialModPrimeMap_surjective A p hp))

/-- 概要：実 mod p 比較同型は商代表元を係数商射で送る。
方針：第一同型定理による同型の代表元公式を使う。
規約：全ての元について述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の多項式評価の比較。 -/
theorem powerRootPolynomialModPrimeEquiv_mk (x : P) :
    powerRootPolynomialModPrimeEquiv A p hp (Ideal.Quotient.mk _ x) =
      powerRootPolynomialModPrimeMap A p hp x := rfl

/-- 概要：係数商射は全根変数を同じ番号の根変数へ送る。
方針：係数 1 の単項式の公式を使う。
規約：任意の段 n を含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック評価の自然性。 -/
theorem powerRootPolynomialModPrimeMap_variable (n : ℕ) :
    powerRootPolynomialModPrimeMap A p hp (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable R p hp n := by
  simp only [powerRootPolynomialVariable, powerRootPolynomialModPrimeMap_single, map_one]

/-- 概要：通常多項式の無限根変数での評価は係数を mod p にする操作と可換。
方針：評価の環射に関する自然性と係数・変数の比較公式を使う。
規約：この恒等式にモニック性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実残余関係式の同定。 -/
theorem powerRootPolynomialModPrimeMap_baseMap (f : Polynomial A) :
    powerRootPolynomialModPrimeMap A p hp (powerRootPolynomialBaseMap A p hp f) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    powerRootPolynomialModPrimeMap_variable, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro a
  exact powerRootPolynomialModPrimeMap_coeff A p hp a


/-- 概要：無限根環のモニック入力は実 mod p 商でも非零因子。
方針：実係数商比較で、係数商上のモニック多項式の既存の正則性へ移す。
規約：元の係数環の p 正則性・非零性・素数性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根環上の実分冪包への正則入力。 -/
theorem powerRootPolynomial_monic_mod_prime_regular (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (P ⧸ Ideal.span {(p : P)})
      (Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootPolynomialBaseMap A p hp f)) := by
  let e := powerRootPolynomialModPrimeEquiv A p hp
  have he : e (Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootPolynomialBaseMap A p hp f)) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
    rw [powerRootPolynomialModPrimeEquiv_mk, powerRootPolynomialModPrimeMap_baseMap]
  have hr := powerRootPolynomial_monic_regular R p hp (f.map bar) (hf.map bar)
  intro x z hxz
  apply e.injective
  apply hr
  have h := congrArg e hxz
  simpa only [smul_eq_mul, map_mul, he] using h

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialModPrime

/-! ## 無限根環と任意の係数主イデアル商

## 概要

無限根多項式環の係数元 c による商は、係数環の c 商上の同じ無限根環と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の R/ϖ 上の具体的な無限根環への比較。

## 方針

係数商射の誘導する環射は全射。その核を各係数で調べて係数主イデアルと同定する。
第一同型定理で実商の同型を得る。

## 規約

p は正。c の正則性、係数環の標数や非零性を要求しない。

## 使われ方

prism の mod p 商内で c=x mod p として、ϖ 係数還元後の入力を比較する。
-/

@[expose] public noncomputable section PowerRootCoefficientQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) (c : A)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "R" => A ⧸ Ideal.span {(c : A)}
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(c : A)})

/-- 概要：各係数を c 商へ送る無限根環の標準環射。
方針：加法モノイド環の係数射を使う。
規約：指数モノイドを保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数還元。 -/
def powerRootCoefficientQuotientMap : P →+* Pbar := AddMonoidAlgebra.mapRingHom G bar

/-- 概要：係数商射は単項式の係数だけを商へ送る。
方針：モノイド環の係数射の公式を使う。
規約：全ての係数・指数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数と変数の照合。 -/
theorem powerRootCoefficientQuotientMap_single (q : G) (b : A) :
    powerRootCoefficientQuotientMap A p hp c (AddMonoidAlgebra.single q b) =
      AddMonoidAlgebra.single q (bar b) := AddMonoidAlgebra.mapRingHom_single _ _ _

/-- 概要：係数商射は標準係数射と可換。
方針：零指数の単項式で計算する。
規約：元の係数環 A の元で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力多項式比較。 -/
theorem powerRootCoefficientQuotientMap_coeff (b : A) :
    powerRootCoefficientQuotientMap A p hp c (algebraMap A P b) =
      algebraMap R Pbar (bar b) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootCoefficientQuotientMap_single A p hp c 0 b

/-- 概要：無限根環の係数商射は全射。
方針：係数商射の全射性を有限台関数へ移す。
規約：係数環の非零性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実商同型。 -/
theorem powerRootCoefficientQuotientMap_surjective :
    Function.Surjective (powerRootCoefficientQuotientMap A p hp c) :=
  AddMonoidAlgebra.map_surjective (bar).toAddMonoidHom Ideal.Quotient.mk_surjective

/-- 概要：係数商射の核は c の係数像の主イデアル。
方針：各係数の c 可除性から単項式を主イデアル内に足し戻す。
規約：c の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の台環の具体的な同定。 -/
theorem powerRootCoefficientQuotientMap_ker :
    RingHom.ker (powerRootCoefficientQuotientMap A p hp c) =
      Ideal.span {algebraMap A P c} := by
  classical
  apply le_antisymm
  · intro x hx
    have hzero : powerRootCoefficientQuotientMap A p hp c x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply (Ideal.span {algebraMap A P c}).sum_mem
    intro q _
    have hcoeff : bar (x.coeff q) = 0 := by
      have h := congrArg (fun z : Pbar => z.coeff q) hzero
      simpa only [powerRootCoefficientQuotientMap, AddMonoidAlgebra.coeff_mapRingHom,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)
    rw [hb]
    have he : AddMonoidAlgebra.single q (c * b) =
        algebraMap A P c * AddMonoidAlgebra.single q b := by
      simp [AddMonoidAlgebra.coe_algebraMap]
    rw [he]
    exact (Ideal.span {algebraMap A P c}).mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    intro t ht
    have ht' : t = algebraMap A P c := Set.mem_singleton_iff.mp ht
    subst t
    change powerRootCoefficientQuotientMap A p hp c (algebraMap A P c) = 0
    rw [powerRootCoefficientQuotientMap_coeff,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c), map_zero]

/-- 概要：無限根環の係数主イデアル商と係数商上の無限根環は環同型。
方針：核と全射性に第一同型定理を使う。
規約：実際の主イデアル商を用い、完備化はしない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の R/ϖ 無限根環への比較。 -/
def powerRootCoefficientQuotientEquiv :
    (P ⧸ Ideal.span {algebraMap A P c}) ≃+* Pbar :=
  (Ideal.quotEquivOfEq (powerRootCoefficientQuotientMap_ker A p hp c).symm).trans
    ((powerRootCoefficientQuotientMap A p hp c).quotientKerEquivOfSurjective
      (powerRootCoefficientQuotientMap_surjective A p hp c))

/-- 概要：係数商比較同型は代表元で係数商射に一致する。
方針：第一同型定理の標準公式を使う。
規約：無限根環の全ての元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力元の照合。 -/
theorem powerRootCoefficientQuotientEquiv_mk (t : P) :
    powerRootCoefficientQuotientEquiv A p hp c (Ideal.Quotient.mk _ t) =
      powerRootCoefficientQuotientMap A p hp c t := rfl

/-- 概要：係数商射は各 p 冪根変数を同じ番号の変数へ送る。
方針：係数 1 の単項式の公式を使う。
規約：全ての段を含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の多項式入力の係数変更。 -/
theorem powerRootCoefficientQuotientMap_variable (n : ℕ) :
    powerRootCoefficientQuotientMap A p hp c (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable R p hp n := by
  simp only [powerRootPolynomialVariable, powerRootCoefficientQuotientMap_single, map_one]

/-- 概要：通常多項式の根変数での評価は係数商と可換。
方針：多項式評価の自然性と係数・変数の公式を使う。
規約：モニック性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の還元後のモニック入力の同定。 -/
theorem powerRootCoefficientQuotientMap_baseMap (f : Polynomial A) :
    powerRootCoefficientQuotientMap A p hp c (powerRootPolynomialBaseMap A p hp f) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    powerRootCoefficientQuotientMap_variable, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro b
  exact powerRootCoefficientQuotientMap_coeff A p hp c b

end SerrePositivity.BhattScholze.Andre

end PowerRootCoefficientQuotient

/-! ## 無限根多項式環の完全 δ 構造

## 概要

完全 δ 係数環上の無限 p 冪根多項式環の標準 δ 構造は完全。
BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻し比較の入力環を具体化する。

## 方針

指数の p 倍は同じ p 冪分母モノイドの加法同型であり、逆は有理数として p で割る。
この指数同型と係数 Frobenius 同型をモノイド環上で合成する。

## 規約

未完備の無限根環を扱う。p 進完備化や prismatic envelope の同定を含まない。

## 使われ方

原典の Frobenius による係数変更を、逆を持つ具体的な δ 環射として扱うための入口。
-/

@[expose] public noncomputable section PowerRootPolynomialPerfectDelta

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp

/-- 概要：無限根指数の p 倍は単射。
方針：有理数としての非零 p 倍を消去する。
規約：指数モノイドの部分型の等式として述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius の単射性。 -/
theorem powerRootExponentPrimeScale_injective :
    Function.Injective (powerRootExponentPrimeScale p) := by
  intro q r h
  apply Subtype.ext
  have hv := congrArg (fun t : G => (t : ℚ)) h
  change (p : ℚ) * (q : ℚ) = (p : ℚ) * (r : ℚ) at hv
  exact mul_left_cancel₀ (by exact_mod_cast (hp).ne' : (p : ℚ) ≠ 0) hv

/-- 概要：無限根指数の p 倍は全射。
方針：q/p の分母条件を元の条件の一段先で確認する。
規約：分母表示の選択によらず有理数として q/p を持ち上げる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の逆 Frobenius の指数。 -/
theorem powerRootExponentPrimeScale_surjective :
    Function.Surjective (powerRootExponentPrimeScale p) := by
  intro q
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (hp).ne'
  have hmem : (q : ℚ) / (p : ℚ) ∈ powerRootExponentMonoid p hp := by
    obtain ⟨n, b, hb⟩ := q.property
    refine ⟨n + 1, b, ?_⟩
    rw [pow_succ]
    calc
      (q : ℚ) / p * ((p : ℚ) ^ n * p) = (q : ℚ) * (p : ℚ) ^ n := by
        field_simp
      _ = b := hb
  refine ⟨⟨(q : ℚ) / p, hmem⟩, ?_⟩
  apply Subtype.ext
  change (p : ℚ) * ((q : ℚ) / p) = (q : ℚ)
  exact mul_div_cancel₀ _ hpQ

/-- 概要：無限根指数の p 倍を加法同型として束ねる。
方針：同じ標準加法射の単射性と全射性を使う。
規約：順方向は p 倍のまま変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の単項式 Frobenius 同型。 -/
def powerRootExponentPrimeScaleEquiv : G ≃+ G :=
  AddEquiv.ofBijective (powerRootExponentPrimeScale p)
    ⟨powerRootExponentPrimeScale_injective p, powerRootExponentPrimeScale_surjective p⟩

variable {A : Type u} [CommRing A]
local notation "P" => PowerRootPolynomial A p hp

/-- 概要：完全係数環上の無限根環の標準 Frobenius は環同型。
方針：係数 Frobenius 同型と指数 p 倍の加法同型をモノイド環へ持ち上げて合成する。
規約：既存の標準 Frobenius と同じ順方向の射。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻しの具体的な係数射。 -/
def powerRootPolynomialPerfectFrobeniusEquiv (D : DeltaStructure p A) (hD : D.IsPerfect) :
    P ≃+* P :=
  (AddMonoidAlgebra.mapRingEquiv G (D.frobeniusEquiv hD)).trans
    (AddMonoidAlgebra.mapDomainRingEquiv A (powerRootExponentPrimeScaleEquiv p))

/-- 概要：構成した Frobenius 同型の順射は既存の標準 Frobenius に一致。
方針：二つのモノイド環の標準写像の合成の定義を使う。
規約：δ 構造を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 完全性の確認。 -/
theorem powerRootPolynomialPerfectFrobeniusEquiv_apply
    (D : DeltaStructure p A) (hD : D.IsPerfect) (t : P) :
    powerRootPolynomialPerfectFrobeniusEquiv p D hD t = powerRootPolynomialFrobenius p D t := rfl

/-- 概要：完全 δ 係数環上の無限根多項式環の標準 δ 構造は完全。
方針：標準 Frobenius を具体的環同型の順射と同定して全単射性を得る。
規約：係数環の p 正則性は完全性から供給する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根入力上の Frobenius 比較。 -/
theorem powerRootPolynomialDelta_isPerfect (D : DeltaStructure p A) (hD : D.IsPerfect) :
    (powerRootPolynomialDelta p hD.p_mul_injective D).IsPerfect := by
  change Function.Bijective (powerRootPolynomialDelta p hD.p_mul_injective D).frobeniusLift
  rw [powerRootPolynomialDelta_frobenius]
  exact (powerRootPolynomialPerfectFrobeniusEquiv p D hD).bijective

variable {σ : Type v}

/-- 概要：完全係数上の無限根環の raw 除算包は Frobenius 係数変更で環同型。
方針：無限根 δ 環の完全性から Frobenius 自己同型を作り、係数自己同型の一般計算を使う。
規約：a/d の包から φ(a)/φ(d) の包への向き。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）、BS 著者版 Corollary 2.39（p.25）の raw 比較の入力。 -/
def powerRootPolynomialDivisionFrobeniusEquiv
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) :
    let E := powerRootPolynomialDelta p hD.p_mul_injective D
    DeltaAdjoinDivision E d a ≃+*
      DeltaAdjoinDivision E (E.frobeniusLift d) (fun s => E.frobeniusLift (a s)) :=
  let E := powerRootPolynomialDelta p hD.p_mul_injective D
  let hE := powerRootPolynomialDelta_isPerfect p D hD
  deltaDivisionCoefficientAutEquiv E (E.frobeniusEquiv hE)
    (E.frobeniusEquiv_isDeltaHom hE) d a

/-- 概要：raw Frobenius 比較は無限根環の係数を Frobenius で送る。
方針：係数自己同型による raw 同型の係数公式を使う。
規約：係数環は無限根入力環全体。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 引戻しの係数作用。 -/
theorem powerRootPolynomialDivisionFrobeniusEquiv_coeff
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) (b : P) :
    let E := powerRootPolynomialDelta p hD.p_mul_injective D
    powerRootPolynomialDivisionFrobeniusEquiv p D hD d a (deltaAdjoinDivisionMap E d a b) =
      deltaAdjoinDivisionMap E (E.frobeniusLift d) (fun s => E.frobeniusLift (a s))
        (E.frobeniusLift b) := by
  let E := powerRootPolynomialDelta p hD.p_mul_injective D
  let hE := powerRootPolynomialDelta_isPerfect p D hD
  exact deltaDivisionCoefficientAutEquiv_coeff E (E.frobeniusEquiv hE)
    (E.frobeniusEquiv_isDeltaHom hE) d a b

/-- 概要：raw Frobenius 比較は初期除算変数の添字を保つ。
方針：係数自己同型による同型の変数公式を使う。
規約：任意の入力族を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック根関係の座標比較。 -/
theorem powerRootPolynomialDivisionFrobeniusEquiv_variable
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) (s : σ) :
    let E := powerRootPolynomialDelta p hD.p_mul_injective D
    powerRootPolynomialDivisionFrobeniusEquiv p D hD d a
      (deltaAdjoinDivisionVariable E d a s) =
        deltaAdjoinDivisionVariable E (E.frobeniusLift d) (fun t => E.frobeniusLift (a t)) s := by
  let E := powerRootPolynomialDelta p hD.p_mul_injective D
  let hE := powerRootPolynomialDelta_isPerfect p D hD
  exact deltaDivisionCoefficientAutEquiv_variable E (E.frobeniusEquiv hE)
    (E.frobeniusEquiv_isDeltaHom hE) d a s

/-- 概要：無限根環の raw Frobenius 比較は実 δ 射。
方針：一般の係数自己同型による比較の δ 互換性を供給する。
規約：完備化前の両商 δ 構造を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後の比較への入力。 -/
theorem powerRootPolynomialDivisionFrobeniusEquiv_isDeltaHom
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : P) (a : σ → P) :
    let E := powerRootPolynomialDelta p hD.p_mul_injective D
    (deltaAdjoinDivisionStructure E d a).IsDeltaHom
      (deltaAdjoinDivisionStructure E (E.frobeniusLift d) (fun s => E.frobeniusLift (a s)))
      (powerRootPolynomialDivisionFrobeniusEquiv p D hD d a).toRingHom := by
  let E := powerRootPolynomialDelta p hD.p_mul_injective D
  let hE := powerRootPolynomialDelta_isPerfect p D hD
  exact deltaDivisionCoefficientAutEquiv_isDeltaHom E (E.frobeniusEquiv hE)
    (E.frobeniusEquiv_isDeltaHom hE) d a

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialPerfectDelta

/-! ## 無限根環と任意の係数イデアル商

## 概要

無限根多項式環を係数イデアル I で割ると A/I 上の同じ無限根環と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の二元商上の入力環を具体化する。

## 方針

係数変更射の全射性と核を有限台関数の各係数で計算する。

## 規約

I の主性・正則性・係数環の非零性を仮定しない。

## 使われ方

(p,d) 商上の主 pd 表示を R/ϖ 上の無限根入力へ移す。
-/

@[expose] public noncomputable section PowerRootCoefficientIdealQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) (I : Ideal A)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "R" => A ⧸ I
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "bar" => Ideal.Quotient.mk I
local notation "J" => I.map (algebraMap A P)

/-- 概要：各係数を I 商へ送る無限根環の標準環射。
方針：加法モノイド環の係数射を使う。
規約：指数モノイドを保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数還元。 -/
def powerRootCoefficientIdealQuotientMap : P →+* Pbar := AddMonoidAlgebra.mapRingHom G bar

/-- 概要：係数商射は単項式の係数だけを商へ送る。
方針：モノイド環の係数射の公式を使う。
規約：全ての係数・指数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数と変数の照合。 -/
theorem powerRootCoefficientIdealQuotientMap_single (q : G) (b : A) :
    powerRootCoefficientIdealQuotientMap A p hp I (AddMonoidAlgebra.single q b) =
      AddMonoidAlgebra.single q (bar b) := AddMonoidAlgebra.mapRingHom_single _ _ _

/-- 概要：係数商射は標準係数射と可換。
方針：零指数の単項式で計算する。
規約：元の係数環 A の元で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力多項式比較。 -/
theorem powerRootCoefficientIdealQuotientMap_coeff (b : A) :
    powerRootCoefficientIdealQuotientMap A p hp I (algebraMap A P b) =
      algebraMap R Pbar (bar b) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootCoefficientIdealQuotientMap_single A p hp I 0 b

/-- 概要：無限根環の係数商射は全射。
方針：係数商射の全射性を有限台関数へ移す。
規約：係数環の非零性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実商同型。 -/
theorem powerRootCoefficientIdealQuotientMap_surjective :
    Function.Surjective (powerRootCoefficientIdealQuotientMap A p hp I) :=
  AddMonoidAlgebra.map_surjective (bar).toAddMonoidHom Ideal.Quotient.mk_surjective

/-- 概要：係数商射の核は 係数イデアル I の像イデアル。
方針：各係数の I への所属から単項式を像イデアル内に足し戻す。
規約：I の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の台環の具体的な同定。 -/
theorem powerRootCoefficientIdealQuotientMap_ker :
    RingHom.ker (powerRootCoefficientIdealQuotientMap A p hp I) =
      J := by
  classical
  apply le_antisymm
  · intro x hx
    have hzero : powerRootCoefficientIdealQuotientMap A p hp I x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply (J).sum_mem
    intro q _
    have hcoeff : bar (x.coeff q) = 0 := by
      have h := congrArg (fun z : Pbar => z.coeff q) hzero
      simpa only [powerRootCoefficientIdealQuotientMap, AddMonoidAlgebra.coeff_mapRingHom,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
    have hcoeffI : x.coeff q ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hcoeff
    have he : AddMonoidAlgebra.single q (x.coeff q) =
        algebraMap A P (x.coeff q) * AddMonoidAlgebra.single q 1 := by
      simp [AddMonoidAlgebra.coe_algebraMap]
    rw [he]
    exact (J).mul_mem_right _ (Ideal.mem_map_of_mem _ hcoeffI)
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change powerRootCoefficientIdealQuotientMap A p hp I (algebraMap A P b) = 0
    rw [powerRootCoefficientIdealQuotientMap_coeff,
      Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]

/-- 概要：無限根環の係数イデアル商と係数商上の無限根環は環同型。
方針：核と全射性に第一同型定理を使う。
規約：実際のイデアル商を用い、完備化はしない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の R/ϖ 無限根環への比較。 -/
def powerRootCoefficientIdealQuotientEquiv :
    (P ⧸ J) ≃+* Pbar :=
  (Ideal.quotEquivOfEq (powerRootCoefficientIdealQuotientMap_ker A p hp I).symm).trans
    ((powerRootCoefficientIdealQuotientMap A p hp I).quotientKerEquivOfSurjective
      (powerRootCoefficientIdealQuotientMap_surjective A p hp I))

/-- 概要：係数商比較同型は代表元で係数商射に一致する。
方針：第一同型定理の標準公式を使う。
規約：無限根環の全ての元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力元の照合。 -/
theorem powerRootCoefficientIdealQuotientEquiv_mk (t : P) :
    powerRootCoefficientIdealQuotientEquiv A p hp I (Ideal.Quotient.mk _ t) =
      powerRootCoefficientIdealQuotientMap A p hp I t := rfl

/-- 概要：係数商射は各 p 冪根変数を同じ番号の変数へ送る。
方針：係数 1 の単項式の公式を使う。
規約：全ての段を含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の多項式入力の係数変更。 -/
theorem powerRootCoefficientIdealQuotientMap_variable (n : ℕ) :
    powerRootCoefficientIdealQuotientMap A p hp I (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable R p hp n := by
  simp only [powerRootPolynomialVariable, powerRootCoefficientIdealQuotientMap_single, map_one]

/-- 概要：通常多項式の根変数での評価は係数商と可換。
方針：多項式評価の自然性と係数・変数の公式を使う。
規約：モニック性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の還元後のモニック入力の同定。 -/
theorem powerRootCoefficientIdealQuotientMap_baseMap (f : Polynomial A) :
    powerRootCoefficientIdealQuotientMap A p hp I (powerRootPolynomialBaseMap A p hp f) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    powerRootCoefficientIdealQuotientMap_variable, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro b
  exact powerRootCoefficientIdealQuotientMap_coeff A p hp I b

end SerrePositivity.BhattScholze.Andre

end PowerRootCoefficientIdealQuotient

/-! ## 互換な根列による無限根指数の評価

## 概要

互換な p 冪根の列は、p 冪分母の非負有理指数から乗法モノイドへの射を定める。
BS 著者版 Remark 7.15（著者版 p.62）の無限根入力環の普遍性の準備。

## 方針

指数の分母表示を選び、異なる表示の値を共通の有限段へ移して照合する。
原典の記述を補う具体的な有理指数による計算である。

## 規約

p の正値性と根列の互換性だけを使う。素数性・標数・ねじれなしは不要。

## 使われ方

元の単項式表示の無限根多項式環から、指定した根列への環評価を作る。
-/

@[expose] public noncomputable section PowerRootExponentEvaluation

namespace SerrePositivity.BhattScholze.Andre
variable {B : Type u} [CommMonoid B] (p : ℕ) (hp : 0 < p)
variable (ρ : ℕ → B)
local notation "G" => powerRootExponentMonoid p hp

/-- 概要：根列の m 段後の p の m 乗冪は元の段へ戻る。
方針：隣接する根関係を m 回帰納的に合成する。
規約：零段の移動も含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母表示を共通段へ移す。 -/
theorem compatiblePowerRoots_iterate (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (n m : ℕ) : ρ (n + m) ^ (p ^ m) = ρ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_mul, show n + (m + 1) = (n + m) + 1 by omega, hρ]
    exact ih

include hp in
/-- 概要：同じ有理指数の二つの表示は根列で同じ値を持つ。
方針：分母を掛けて自然数指数を比較し、二つの段を共通の和の段へ移す。
規約：根列の元の単射性や非零性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の指数評価の表示独立性。 -/
theorem compatiblePowerRoots_repr_eq (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n k m l : ℕ)
    (h : (k : ℚ) / (p : ℚ) ^ n = (l : ℚ) / (p : ℚ) ^ m) :
    ρ n ^ k = ρ m ^ l := by
  have hz : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have he : k * p ^ m = l * p ^ n := by
    exact_mod_cast (div_eq_div_iff (pow_ne_zero n hz) (pow_ne_zero m hz)).mp h
  rw [← compatiblePowerRoots_iterate p ρ hρ n m,
    ← compatiblePowerRoots_iterate p ρ hρ m n, ← pow_mul, ← pow_mul]
  rw [Nat.add_comm m n, Nat.mul_comm (p ^ m) k, Nat.mul_comm (p ^ n) l, he]

/-- 概要：無限根指数を、その分母表示を選んで根列の冪へ評価する。
方針：存在する自然数分子と p 冪分母を選択する。
規約：この定義自体は根列の互換性を使わず、表示独立性は次の補題で示す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の単項式評価の指数側。 -/
def powerRootExponentEval (q : G) : B :=
  let h := powerRootExponent_exists_repr p hp q
  ρ h.choose ^ h.choose_spec.choose

/-- 概要：選んだ表示による指数評価は任意の有限段表示で計算できる。
方針：選択した分母表示と与えた表示に表示独立性を適用する。
規約：分母を掛けた等式として入力する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の評価の加法・変数公式。 -/
theorem powerRootExponentEval_of_repr (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (q : G) (n k : ℕ)
    (hq : (q : ℚ) * (p : ℚ) ^ n = k) : powerRootExponentEval p hp ρ q = ρ n ^ k := by
  let h := powerRootExponent_exists_repr p hp q
  change ρ h.choose ^ h.choose_spec.choose = ρ n ^ k
  apply compatiblePowerRoots_repr_eq p hp ρ hρ
  exact h.choose_spec.choose_spec.symm.trans
    ((eq_div_iff (pow_ne_zero n (by exact_mod_cast hp.ne'))).mpr hq)

/-- 概要：無限根指数の加法を根列の値の乗法へ送るモノイド射。
方針：二つの分母を共通段へ揃え、冪の和・積の公式を使う。
規約：指数の加法モノイドには Multiplicative を付けて乗法として扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根多項式環の普遍射。 -/
def powerRootExponentEvalHom (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) : Multiplicative G →* B where
  toFun q := powerRootExponentEval p hp ρ q.toAdd
  map_one' := by
    exact (powerRootExponentEval_of_repr p hp ρ hρ 0 0 0 (by simp)).trans (pow_zero _)
  map_mul' q r := by
    obtain ⟨n, k, hq⟩ := q.toAdd.property
    obtain ⟨m, l, hr⟩ := r.toAdd.property
    have hsum : ((q.toAdd + r.toAdd : G) : ℚ) * (p : ℚ) ^ (n + m) =
        (k * p ^ m + l * p ^ n : ℕ) := by
      push_cast
      change ((q.toAdd : ℚ) + (r.toAdd : ℚ)) * (p : ℚ) ^ (n + m) = _
      calc
        _ = ((q.toAdd : ℚ) * (p : ℚ) ^ n) * (p : ℚ) ^ m +
            ((r.toAdd : ℚ) * (p : ℚ) ^ m) * (p : ℚ) ^ n := by rw [pow_add]; ring
        _ = _ := by rw [hq, hr]
    change powerRootExponentEval p hp ρ (q.toAdd + r.toAdd) =
      powerRootExponentEval p hp ρ q.toAdd * powerRootExponentEval p hp ρ r.toAdd
    rw [powerRootExponentEval_of_repr p hp ρ hρ _ (n + m) _ hsum,
      powerRootExponentEval_of_repr p hp ρ hρ _ n k hq,
      powerRootExponentEval_of_repr p hp ρ hρ _ m l hr, pow_add,
      Nat.mul_comm k (p ^ m), pow_mul, compatiblePowerRoots_iterate p ρ hρ n m,
      Nat.mul_comm l (p ^ n), pow_mul, Nat.add_comm n m,
      compatiblePowerRoots_iterate p ρ hρ m n]

/-- 概要：第 n 根変数の指数の評価は指定根列の第 n 元。
方針：分子 1、分母 p の n 乗の表示で評価する。
規約：全段 n を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の根の像を保つ。 -/
theorem powerRootExponentEvalHom_variable (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    powerRootExponentEvalHom p hp ρ hρ (Multiplicative.ofAdd (powerRootVariableExponent p hp n)) =
      ρ n := by
  change powerRootExponentEval p hp ρ (powerRootVariableExponent p hp n) = ρ n
  rw [powerRootExponentEval_of_repr p hp ρ hρ _ n 1
    (by
      change (1 / (p : ℚ) ^ n) * (p : ℚ) ^ n = 1
      exact div_mul_cancel₀ _ (pow_ne_zero n (by exact_mod_cast hp.ne'))), pow_one]

end SerrePositivity.BhattScholze.Andre

end PowerRootExponentEvaluation

/-! ## André A1-a：無限根多項式環の任意の係数主商

## 概要

無限根多項式環の任意の係数元による商は、係数環をその元で割った無限根環と同型。
モニック入力は各係数 p 冪商で正則となる。BS 著者版 Remark 7.15（著者版 p.62）の完備入力。

## 方針

既存の mod p 比較の係数ごとの核計算を任意の係数元に一般化する。
原典を補う具体的な単項式の計算とモニック正則性による経路。

## 規約

根の指数を定める p と、係数商の元 a を区別する。p 正則性・素数性は不要。

## 使われ方

モニック商と p 完備化の交換に必要な、全 p 冪商での正則性を供給する。
-/

@[expose] public noncomputable section PowerRootPolynomialModScalar

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable (A : Type u) [CommRing A] (p : ℕ) (hp : 0 < p) (a : A)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "R" => A ⧸ Ideal.span {(a : A)}
local notation "Pbar" => PowerRootPolynomial R p hp
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(a : A)})

/-- 概要：無限根多項式の係数を a 主商へ写す環射。
方針：同じ指数モノイド上の係数環射を使う。
規約：根の段や指数を変えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数冪商比較。 -/
def powerRootPolynomialModScalarMap : P →+* Pbar :=
  AddMonoidAlgebra.mapRingHom G bar

/-- 概要：係数主商への無限根環の射は全射。
方針：係数商射の全射性を有限支持の係数写像へ移す。
規約：任意の係数元 a を許す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実主商同型。 -/
theorem powerRootPolynomialModScalarMap_surjective :
    Function.Surjective (powerRootPolynomialModScalarMap A p hp a) :=
  AddMonoidAlgebra.map_surjective (bar).toAddMonoidHom Ideal.Quotient.mk_surjective

/-- 概要：係数主商への無限根環の射の核は係数 a の像の主イデアル。
方針：各係数を a の倍数に書き、有限和へ戻す。
規約：a の正則性や p との関係は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実係数商の同定。 -/
theorem powerRootPolynomialModScalarMap_ker :
    RingHom.ker (powerRootPolynomialModScalarMap A p hp a) =
      Ideal.span {algebraMap A P a} := by
  classical
  apply le_antisymm
  · intro x hx
    have hzero : powerRootPolynomialModScalarMap A p hp a x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply (Ideal.span {algebraMap A P a}).sum_mem
    intro q _
    have hcoeff : bar (x.coeff q) = 0 := by
      have h := congrArg (fun z : Pbar => z.coeff q) hzero
      simpa only [powerRootPolynomialModScalarMap, AddMonoidAlgebra.coeff_mapRingHom,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)
    rw [hb]
    have he : AddMonoidAlgebra.single q (a * b) =
        algebraMap A P a * AddMonoidAlgebra.single q b := by
      change AddMonoidAlgebra.single q (a * b) =
        AddMonoidAlgebra.single 0 a * AddMonoidAlgebra.single q b
      rw [AddMonoidAlgebra.single_mul_single, zero_add]
    rw [he]
    exact (Ideal.span {algebraMap A P a}).mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = _)
    change powerRootPolynomialModScalarMap A p hp a (algebraMap A P a) = 0
    simp [powerRootPolynomialModScalarMap, AddMonoidAlgebra.coe_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)]

/-- 概要：無限根環の係数 a 商は係数主商上の無限根環と環同型。
方針：核の同定と全射性から第一同型定理を使う。
規約：同じ実指数型を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック正則性の移送。 -/
def powerRootPolynomialModScalarEquiv :
    (P ⧸ Ideal.span {algebraMap A P a}) ≃+* Pbar :=
  (Ideal.quotEquivOfEq (powerRootPolynomialModScalarMap_ker A p hp a).symm).trans
    ((powerRootPolynomialModScalarMap A p hp a).quotientKerEquivOfSurjective
      (powerRootPolynomialModScalarMap_surjective A p hp a))

/-- 概要：係数主商同型は代表元を係数ごとの商射で送る。
方針：第一同型定理の定義を展開する。
規約：全ての無限根多項式に適用する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力の追跡。 -/
theorem powerRootPolynomialModScalarEquiv_mk (x : P) :
    powerRootPolynomialModScalarEquiv A p hp a (Ideal.Quotient.mk _ x) =
      powerRootPolynomialModScalarMap A p hp a x := rfl

/-- 概要：モニック入力は任意の係数主商上で正則。
方針：係数主商同型に沿って、係数商上のモニック入力の正則性を戻す。
規約：a の正則性・非零性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全 p 冪商での入力正則性。 -/
theorem powerRootPolynomial_monic_mod_scalar_regular (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (P ⧸ Ideal.span {algebraMap A P a})
      (Ideal.Quotient.mk (Ideal.span {algebraMap A P a})
        (powerRootPolynomialBaseMap A p hp f)) := by
  let e := powerRootPolynomialModScalarEquiv A p hp a
  have he : e (Ideal.Quotient.mk _ (powerRootPolynomialBaseMap A p hp f)) =
      powerRootPolynomialBaseMap R p hp (f.map bar) := by
    rw [powerRootPolynomialModScalarEquiv_mk]
    unfold powerRootPolynomialBaseMap
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
      Polynomial.eval₂_map]
    have hv : powerRootPolynomialModScalarMap A p hp a
        (powerRootPolynomialVariable A p hp 0) = powerRootPolynomialVariable R p hp 0 := by
      simp only [powerRootPolynomialVariable, powerRootPolynomialModScalarMap,
        AddMonoidAlgebra.mapRingHom_single, map_one]
    rw [hv]
    congr 1
    apply RingHom.ext
    intro b
    change powerRootPolynomialModScalarMap A p hp a (algebraMap A P b) =
      algebraMap R Pbar (bar b)
    simp [powerRootPolynomialModScalarMap, AddMonoidAlgebra.coe_algebraMap]
  have hr := powerRootPolynomial_monic_regular R p hp (f.map bar) (hf.map bar)
  intro x y hxy
  apply e.injective
  apply hr
  simpa only [smul_eq_mul, map_mul, he] using congrArg e hxy

/-- 概要：モニック入力は全ての p 冪商で正則。
方針：任意の係数主商の結果を pⁿ に適用する。
規約：係数環の p 正則性を追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化とモニック商の交換。 -/
theorem powerRootPolynomial_monic_mod_prime_power_regular
    (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    IsSMulRegular (P ⧸ Ideal.span {(p : P) ^ n})
      (Ideal.Quotient.mk (Ideal.span {(p : P) ^ n}) (powerRootPolynomialBaseMap A p hp f)) := by
  have h := powerRootPolynomial_monic_mod_scalar_regular A p hp ((p : A) ^ n) f hf
  rw [map_pow, map_natCast] at h
  exact h

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialModScalar
