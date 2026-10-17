module

public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# André E1・E2：p 冪根多項式の指数と整数・小数部分の分解

## 概要

p 冪分母を持つ非負有理数の加法モノイドを具体的に構成し、
各指数を自然数部分と 1 未満の指数に一意に分解する。
BS Rem 7.15（著者版 p.62）の無限 p 冪根変数の自由基底の準備。

## 方針

q pⁿ が自然数となる有理数を使う。加法は分母を pⁿ⁺ᵐ に揃えて閉じる。
有理数の床関数と小数部分を使い、同じ p 冪分母を保つことを剰余計算で示す。

## 規約

p の正値性だけを使い、素数性・係数環の標数は不要。
これは原典の pd 計算を補足する指数の具体的計算であり、prism の同定は含まない。

## 使われ方

単項式基底と、多項式環上の小数指数による自由基底に使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：p 冪分母を持つ非負有理数の加法モノイド。
方針：分母を共通の p 冪にして加法の閉性を証明する。
規約：p は正とする。台集合には分母条件だけを書き、非負性は後で導く。
使われ方：BS Rem 7.15（著者版 p.62）の無限 p 冪根単項式の指数。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の通常変数の整数冪。 -/
def powerRootNatExponent (p : ℕ) (hp : 0 < p) (n : ℕ) : powerRootExponentMonoid p hp :=
  ⟨n, 0, n, by simp⟩

/-- 概要：全ての p 冪根指数は非負。
方針：正の p 冪を掛けた値が自然数であることを使う。
規約：有理数としての順序で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の床関数による指数分解。 -/
theorem powerRootExponent_nonneg (p : ℕ) (hp : 0 < p) (q : powerRootExponentMonoid p hp) :
    0 ≤ (q : ℚ) := by
  obtain ⟨n, a, ha⟩ := q.property
  have hpos : 0 < (p : ℚ) ^ n := pow_pos (by exact_mod_cast hp) _
  exact (mul_nonneg_iff_of_pos_right hpos).mp (ha.symm ▸ Nat.cast_nonneg a)

/-- 概要：各指数は自然数を p 冪で割った形に書ける。
方針：定義の分母条件を、非零分母で割り戻す。
規約：非負の分子を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の有限段の単項式への帰着。 -/
theorem powerRootExponent_exists_repr (p : ℕ) (hp : 0 < p)
    (q : powerRootExponentMonoid p hp) :
    ∃ n a : ℕ, (q : ℚ) = a / (p : ℚ) ^ n := by
  obtain ⟨n, a, ha⟩ := q.property
  exact ⟨n, a, (eq_div_iff (pow_ne_zero _ (by exact_mod_cast hp.ne'))).mpr ha⟩

/-- 概要：1 未満の p 冪根指数の型。
方針：非負指数モノイドの部分型を取る。
規約：零指数も含める。
使われ方：BS Rem 7.15（著者版 p.62）の通常多項式環上の基底の添字。 -/
abbrev PowerRootFraction (p : ℕ) (hp : 0 < p) :=
  {q : powerRootExponentMonoid p hp // (q : ℚ) < 1}

/-- 概要：小数部分を取っても指数の p 冪分母条件は保たれる。
方針：a/pⁿ の小数部分を (a mod pⁿ)/pⁿ と計算する。
規約：有理数の小数部分を同じ指数モノイドへ戻す。
使われ方：BS Rem 7.15（著者版 p.62）の自由基底の整数部分との分離。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の基底添字同値の計算。 -/
theorem powerRootFractionalPart_val (p : ℕ) (hp : 0 < p) (q : powerRootExponentMonoid p hp) :
    ((powerRootFractionalPart p hp q).val : ℚ) = Int.fract (q : ℚ) := rfl

/-- 概要：各指数は自然数部分と 1 未満の指数に一意に分解する。
方針：床関数・小数部分と、それらの和による逆写像を使う。
規約：分解の逆は自然数指数と小数指数の加法そのもの。
使われ方：BS Rem 7.15（著者版 p.62）の無限 p 冪根多項式環の自由基底。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の互換な冪根変数。 -/
def powerRootVariableExponent (p : ℕ) (hp : 0 < p) (n : ℕ) :
    powerRootExponentMonoid p hp :=
  ⟨1 / (p : ℚ) ^ n, n, 1, div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hp.ne'))⟩

/-- 概要：隣接する冪根変数の指数を p 倍すると前の指数になる。
方針：正の p 冪を用いて有理数の等式を計算する。
規約：モノイド上の p 倍は加法的な自然数作用。
使われ方：BS Rem 7.15（著者版 p.62）の Yₙ₊₁ᵖ=Yₙ。 -/
theorem powerRootVariableExponent_nsmul (p : ℕ) (hp : 0 < p) (n : ℕ) :
    p • powerRootVariableExponent p hp (n + 1) = powerRootVariableExponent p hp n := by
  apply Subtype.ext
  change p • (1 / (p : ℚ) ^ (n + 1)) = 1 / (p : ℚ) ^ n
  rw [nsmul_eq_mul, pow_succ']
  field_simp

/-- 概要：全指数は一つの冪根変数の自然数倍として表される。
方針：p 冪分母の表示を自然数作用へ書き直す。
規約：段 n と冪 k は指数に依存して選べる。
使われ方：BS Rem 7.15（著者版 p.62）の無限変数環を有限段から生成する。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の通常変数の作用と小数指数基底の整合性。 -/
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
