module

public import SerrePositivity.AlgebraicGeometry.ChartEmbedding

/-!
概要：KST §5、Stacks 080Y の中心の降下に使う、指定次数のチャート分数。
方針：Iⁿ の元 r に対し斉次分数 (r tⁿ)/(a t)ⁿ を構成し、正則な分母消去で計算する。
規約：基礎環での a の正則性は不要。
使われ方：blowup 上の中心の斉次な分子による記述。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open Polynomial HomogeneousLocalization
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)

/--
概要：標準チャートで正則な係数元の冪は等式を検出する。
方針：差を取り、非零因子の冪の消去を使う。
規約：KST §5、Stacks 080Y、非被約な環を許す。
使われ方：指定次数の分数の演算公式。
-/
theorem chart_mul_base_pow_injective (n : ℕ) :
    Function.Injective (fun z : BlowupChartRing I a => z * chartBaseMap I a a.1 ^ n) := by
  intro x y h
  dsimp only at h
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_right.mp
    ((nonZeroDivisors _).pow_mem (chartBaseMap_mem_nonZeroDivisors I a) n)) (x - y)
  rw [sub_mul, h, sub_self]

/--
概要：Iⁿ の元を分子に持つ指定次数の標準チャート分数。
方針：Rees 単項式を次数一元の n 乗で割る。
規約：KST §5、Stacks 080Y、分子の所属を部分型で保つ。
使われ方：中心の降下に使う斉次切断の記述。
-/
def chartFraction (n : ℕ) (r : ↥(I ^ n)) : BlowupChartRing I a :=
  Away.mk (reesGrade I) (reesDegreeOne_mem I a) n (reesMonomial I n r)
    (by simpa using reesMonomial_mem I n r)

/--
概要：指定次数のチャート分数は aⁿ を掛けると分子の係数像になる。
方針：斉次分母消去を Rees 単項式に適用する。
規約：KST §5、Stacks 080Y、基礎環の単射性を仮定しない。
使われ方：分数の加法・乗法・係数作用の計算。
-/
theorem chartFraction_clear (n : ℕ) (r : ↥(I ^ n)) :
    chartFraction I a n r * chartBaseMap I a a.1 ^ n = chartBaseMap I a r.1 := by
  simpa only [chartFraction, reesMonomial, coeff_monomial_same] using
    chart_mk_clear_denominator I a n (reesMonomial I n r) (reesMonomial_mem I n r)

/--
概要：指定次数の分数は分子の加法を保つ。
方針：同じ正則な分母を払い、係数写像の加法性で比較する。
規約：KST §5、Stacks 080Y、分子は Iⁿ の元。
使われ方：斉次な分子の条件が加法で閉じることの証明。
-/
@[simp] theorem chartFraction_add (n : ℕ) (r s : ↥(I ^ n)) :
    chartFraction I a n (r + s) = chartFraction I a n r + chartFraction I a n s := by
  apply chart_mul_base_pow_injective I a n
  dsimp only
  rw [add_mul, chartFraction_clear, chartFraction_clear, chartFraction_clear]
  exact map_add (chartBaseMap I a) r.1 s.1

/--
概要：指定次数の分数は零分子を零に送る。
方針：正則な分母を払って零を判定する。
規約：KST §5、Stacks 080Y、零環も含む。
使われ方：斉次な分子の条件の零元。
-/
@[simp] theorem chartFraction_zero (n : ℕ) : chartFraction I a n 0 = 0 := by
  apply chart_mul_base_pow_injective I a n
  dsimp only
  rw [chartFraction_clear, zero_mul]
  exact map_zero _

/--
概要：指定次数の分数への基礎環の係数作用は分子への乗法に一致する。
方針：同じ正則な分母を払い、係数写像の乗法性を使う。
規約：KST §5、Stacks 080Y、係数作用を環準同型で明示する。
使われ方：斉次な分子の条件がイデアルを与えることの証明。
-/
theorem chartFraction_smul (n : ℕ) (c : R) (r : ↥(I ^ n)) :
    chartFraction I a n (c • r) = chartBaseMap I a c * chartFraction I a n r := by
  apply chart_mul_base_pow_injective I a n
  dsimp only
  rw [chartFraction_clear, mul_assoc, chartFraction_clear, ← map_mul]
  rfl

/--
概要：異なる次数の二分数の積は分子を掛けて次数を足した分数。
方針：a^(n+m) を払い、二つの分母消去式を掛ける。
規約：KST §5、Stacks 080Y、分子の積は I^(n+m) に属する。
使われ方：降下に使う斉次イデアルの乗法閉性。
-/
theorem chartFraction_mul (n m : ℕ) (r : ↥(I ^ n)) (s : ↥(I ^ m)) :
    chartFraction I a (n + m)
        ⟨r.1 * s.1, by rw [pow_add]; exact Ideal.mul_mem_mul r.2 s.2⟩ =
      chartFraction I a n r * chartFraction I a m s := by
  apply chart_mul_base_pow_injective I a (n + m)
  dsimp only
  rw [chartFraction_clear]
  dsimp only
  rw [pow_add]
  calc
    _ = (chartFraction I a n r * chartBaseMap I a a.1 ^ n) *
        (chartFraction I a m s * chartBaseMap I a a.1 ^ m) := by
      rw [chartFraction_clear, chartFraction_clear, ← map_mul]
    _ = _ := by ring

/--
概要：中心元 b の n 乗を分子とする分数は比 b/a の n 乗。
方針：aⁿ を払い、a · (b/a) = b の n 乗を使う。
規約：KST §5、Stacks 080Y、中心元の冪の所属を保持する。
使われ方：重なりで比の冪を掛けた分数を次数を増やした分子に戻す。
-/
theorem chartFraction_center_pow (b : I) (n : ℕ) :
    chartFraction I a n ⟨b.1 ^ n, Ideal.pow_mem_pow b.2 n⟩ = chartRatio I a b ^ n := by
  apply chart_mul_base_pow_injective I a n
  dsimp only
  rw [chartFraction_clear]
  dsimp only
  rw [← mul_pow, mul_comm (chartRatio I a b), chartBaseMap_mul_ratio, map_pow]

/--
概要：中心元自身の n 乗を分子とする分数は一。
方針：正則な aⁿ を払い、係数写像の冪保存を使う。
規約：KST §5、Stacks 080Y、零環も含む。
使われ方：分子と分母の次数を同時に増やす。
-/
@[simp] theorem chartFraction_self_pow (n : ℕ) :
    chartFraction I a n ⟨a.1 ^ n, Ideal.pow_mem_pow a.2 n⟩ = 1 := by
  apply chart_mul_base_pow_injective I a n
  dsimp only
  rw [chartFraction_clear, one_mul]
  exact map_pow _ _ _

/--
概要：分子へ aᵐ を補い次数を m 増やしても、a チャート上の分数は変わらない。
方針：分数の積公式と aᵐ/aᵐ = 1 を使う。
規約：KST §5、Stacks 080Y、分子の中心冪への所属を保持する。
使われ方：降下イデアルの次数の共通化。
-/
theorem chartFraction_shift_self (n m : ℕ) (r : ↥(I ^ n)) :
    chartFraction I a (n + m)
      ⟨r.1 * a.1 ^ m, by rw [pow_add]; exact Ideal.mul_mem_mul r.2 (Ideal.pow_mem_pow a.2 m)⟩ =
        chartFraction I a n r := by
  rw [chartFraction_mul I a n m r ⟨a.1 ^ m, Ideal.pow_mem_pow a.2 m⟩,
    chartFraction_self_pow, mul_one]

/--
概要：標準チャートの任意の元は指定次数の分数として表示できる。
方針：斉次分母消去の分子を取り、正則な分母で分数と元を比較する。
規約：KST §5、Stacks 080Y、分子は Iⁿ に属する。
使われ方：有限生成イデアルの生成元を斉次な分子で表す。
-/
theorem exists_chartFraction (z : BlowupChartRing I a) :
    ∃ (n : ℕ) (r : ↥(I ^ n)), chartFraction I a n r = z := by
  obtain ⟨n, r, hr, hz⟩ := chart_clear_denominator_mem I a z
  refine ⟨n, ⟨r, hr⟩, chart_mul_base_pow_injective I a n ?_⟩
  dsimp only
  rw [chartFraction_clear, hz]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
