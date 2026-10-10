module

public import SerrePositivity.Asymptotic.FreeSequence
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.CategoryTheory.Retract

/-!
# 自由加群列の一様なランク上界と生成元

正規化列が各項で正ならば、通常の `O(s)` 条件は全項に共通する整数倍の
上界に強められる。有限個の例外も一つの定数に吸収する。
各段の標準自由加群の分裂全射を組み合わせ、任意の自由列が
標準列の固定整数倍の直和因子になることを示す。
-/

@[expose] public section

namespace SerrePositivity.Asymptotic

open CategoryTheory Filter Asymptotics

/-- 正の整数列に対する `O` 条件は、全項で有効な整数係数の上界を与える。 -/
lemma exists_uniform_nat_bound {r s : ℕ → ℕ} (hs : ∀ n, 0 < s n)
    (hr : (fun n ↦ (r n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ))) :
    ∃ d : ℕ, ∀ n, r n ≤ d * s n := by
  obtain ⟨c, hc⟩ := hr.bound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  obtain ⟨d, hd⟩ := exists_nat_gt c
  refine ⟨max d ((Finset.range N).sup r), fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · have h : (r n : ℝ) ≤ (d : ℝ) * (s n : ℝ) := by
      calc
        (r n : ℝ) ≤ c * (s n : ℝ) := by simpa only [Real.norm_natCast] using hN n hn
        _ ≤ (d : ℝ) * (s n : ℝ) := mul_le_mul_of_nonneg_right hd.le (Nat.cast_nonneg _)
    exact (by exact_mod_cast h : r n ≤ d * s n).trans
      (Nat.mul_le_mul_right _ (le_max_left ..))
  · exact (Finset.le_sup (f := r) (Finset.mem_range.mpr (by omega))).trans
      ((le_max_right d _).trans (Nat.le_mul_of_pos_right _ (hs n)))

namespace FreeSequence

variable {R : Type*} [CommRing R] {s : ℕ → ℕ}

/-- ランクを固定された自然数倍にした自由加群列。 -/
def multiple (X : FreeSequence R s) (d : ℕ) : FreeSequence R s :=
  ⟨fun n ↦ d * X.rank n, by
    simpa only [Nat.cast_mul] using X.rank_isBigO.const_mul_left (d : ℝ)⟩

/-- 項ごとのランク不等式は、自由加群列の実際の retract を与える。 -/
lemma nonempty_retract_of_rank_le (X Y : FreeSequence R s)
    (h : ∀ n, X.rank n ≤ Y.rank n) : Nonempty (Retract X Y) := by
  let p : Y ⟶ X := fun n ↦ LinearMap.funLeft R R (Fin.castLE (h n))
  have hp (n : ℕ) : Function.Surjective (p n) :=
    LinearMap.funLeft_surjective_of_injective R R _ (Fin.castLE_injective (h n))
  choose i hi using fun n ↦ Module.projective_lifting_property (p n) LinearMap.id (hp n)
  exact ⟨⟨i, p, funext hi⟩⟩

/-- 任意の自由列は、標準列の固定整数倍の直和因子である。
整数 `d` は列の添字に依存せず、射の係数への制限も不要。 -/
lemma exists_retract_generator_multiple (hs : ∀ n, 0 < s n) (X : FreeSequence R s) :
    ∃ d : ℕ, Nonempty (Retract X ((generator R s).multiple d)) := by
  obtain ⟨d, hd⟩ := exists_uniform_nat_bound hs X.rank_isBigO
  exact ⟨d, nonempty_retract_of_rank_le X _ hd⟩

end FreeSequence

end SerrePositivity.Asymptotic
