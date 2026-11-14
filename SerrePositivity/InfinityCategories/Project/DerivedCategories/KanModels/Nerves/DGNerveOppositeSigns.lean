module
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic
/-!
概要：dg nerve の頂点反転で必要な全次数の符号と、HA 微分式の整合性。
方針：濃度 m の符号を (-1)^(choose(m,2)-1) とし、左右切断の Koszul 符号を計算する。
規約：二点成分は符号 +1。使われ方：β5 の dg 反対模型と ∞ 反対圏の比較。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- m 点成分の順序反転の符号。 -/
def sign (m : ℕ) : ℤˣ := ((m.choose 2 : ℤ) - 1).negOnePow
/-- 二点成分、すなわち実辺は符号を変えない。 -/
@[simp] lemma sign_two : sign 2 = 1 := by norm_num [sign, Int.negOnePow]
/-- 二回反転すると元の全成分へ戻る。 -/
@[simp] lemma sign_mul_self (m : ℕ) : sign m * sign m = 1 := Int.units_mul_self _
/-- 点を一つ減らす微分項に必要な符号漸化式。 -/
lemma sign_succ (m : ℕ) : sign (m + 1) = (m : ℤ).negOnePow * sign m := by
  unfold sign
  rw [Nat.choose_succ_succ' m 1, Nat.choose_one_right, Nat.cast_add]
  rw [show (m : ℤ) + (m.choose 2 : ℤ) - 1 =
    (m : ℤ) + ((m.choose 2 : ℤ) - 1) by ring, Int.negOnePow_add]
/-- choose(m,2) の二倍を、整数の多項式として計算する。 -/
lemma twice_choose_two (m : ℕ) : 2 * (m.choose 2 : ℤ) = (m : ℤ) * (m - 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.choose_succ_succ m 1, Nat.choose_one_right, Nat.cast_add, Nat.cast_add,
      Nat.cast_one]
    nlinarith
/-- 左右切断の濃度等式に沿う、反転符号の実整数指数の計算。 -/
lemma choose_split (m l r : ℕ) (h : m + 1 = l + r) :
    (m.choose 2 : ℤ) = (l.choose 2 : ℤ) + (r.choose 2 : ℤ) + (l - 1) * (r - 1) := by
  have hm : (m : ℤ) + 1 = (l : ℤ) + (r : ℤ) := by exact_mod_cast h
  have h₀ := twice_choose_two m
  have h₁ := twice_choose_two l
  have h₂ := twice_choose_two r
  have he : (m : ℤ) = (l : ℤ) + (r : ℤ) - 1 := by omega
  rw [he] at h₀
  nlinarith
/-- 元と反転後の HA 合成項の符号は、dg 反対圏の Koszul 符号ごと一致する。 -/
lemma sign_split (m l r : ℕ) (h : m + 1 = l + r) :
    sign m * ((l : ℤ) - 1).negOnePow =
      ((r : ℤ) - 1).negOnePow * sign l * sign r *
        ((2 - (l : ℤ)) * (2 - (r : ℤ))).negOnePow := by
  simp only [sign, ← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).mpr
  refine ⟨(l : ℤ) - 1, ?_⟩
  have hc := choose_split m l r h
  nlinarith
end SerrePositivity.InfinityCategories.Project.DerivedCategories
