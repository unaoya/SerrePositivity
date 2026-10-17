module

public import SerrePositivity.BhattScholze.Andre.PowerRootExponents

/-!
# André E1・E2：互換な根列による無限根指数の評価

## 概要

互換な p 冪根の列は、p 冪分母の非負有理指数から乗法モノイドへの射を定める。
BS Rem 7.15（著者版 p.62）の無限根入力環の普遍性の準備。

## 方針

指数の分母表示を選び、異なる表示の値を共通の有限段へ移して照合する。
原典の記述を補う具体的な有理指数による計算である。

## 規約

p の正値性と根列の互換性だけを使う。素数性・標数・ねじれなしは不要。

## 使われ方

元の単項式表示の無限根多項式環から、指定した根列への環評価を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {B : Type u} [CommMonoid B] (p : ℕ) (hp : 0 < p)
variable (ρ : ℕ → B)
local notation "G" => powerRootExponentMonoid p hp

/-- 概要：根列の m 段後の p の m 乗冪は元の段へ戻る。
方針：隣接する根関係を m 回帰納的に合成する。
規約：零段の移動も含む。
使われ方：BS Rem 7.15（著者版 p.62）の分母表示を共通段へ移す。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の指数評価の表示独立性。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の単項式評価の指数側。 -/
def powerRootExponentEval (q : G) : B :=
  let h := powerRootExponent_exists_repr p hp q
  ρ h.choose ^ h.choose_spec.choose

/-- 概要：選んだ表示による指数評価は任意の有限段表示で計算できる。
方針：選択した分母表示と与えた表示に表示独立性を適用する。
規約：分母を掛けた等式として入力する。
使われ方：BS Rem 7.15（著者版 p.62）の評価の加法・変数公式。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の無限根多項式環の普遍射。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の元の根の像を保つ。 -/
theorem powerRootExponentEvalHom_variable (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    powerRootExponentEvalHom p hp ρ hρ (Multiplicative.ofAdd (powerRootVariableExponent p hp n)) =
      ρ n := by
  change powerRootExponentEval p hp ρ (powerRootVariableExponent p hp n) = ρ n
  rw [powerRootExponentEval_of_repr p hp ρ hρ _ n 1
    (by
      change (1 / (p : ℚ) ^ n) * (p : ℚ) ^ n = 1
      exact div_mul_cancel₀ _ (pow_ne_zero n (by exact_mod_cast hp.ne'))), pow_one]

end SerrePositivity.BhattScholze.Andre
