module

public import SerrePositivity.EInfinity.BarrattEccles.Simplicial
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Barratt–Eccles の非退化単体

概要：Berger–Fresse §1.1 の正規化鎖の基底を非退化な置換列として記述する。
方針：退化写像の像を隣接する二頂点の一致で特徴づける。
規約：q 単体の隣接対は Fin q で添字づける。
使われ方：正規化鎖の群作用と自由基底の構成に用いる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：面写像は指定された頂点を除去する（Berger–Fresse §1.1）。
方針：nerve の面写像を頂点列で評価する。
規約：simplicial の次数 q+1 から q への面写像。
使われ方：正規化鎖の微分の成分を計算する。 -/
@[simp] lemma simplexEquiv_δ (n q : ℕ) (i : Fin (q + 2))
    (x : (simplicial n) _⦋q + 1⦌) (j : Fin (q + 1)) :
    simplexEquiv n q ((simplicial n).δ i x) j =
      simplexEquiv n (q + 1) x (i.succAbove j) := rfl

/-- 概要：退化写像は指定された頂点を複製する（Berger–Fresse §1.1）。
方針：nerve の退化写像を頂点列で評価する。
規約：simplicial の次数 q から q+1 への退化写像。
使われ方：退化単体の特徴づけに用いる。 -/
@[simp] lemma simplexEquiv_σ (n q : ℕ) (i : Fin (q + 1))
    (x : (simplicial n) _⦋q⦌) (j : Fin (q + 2)) :
    simplexEquiv n (q + 1) ((simplicial n).σ i x) j =
      simplexEquiv n q x (i.predAbove j) := rfl

/-- 概要：一つの退化写像の像は対応する隣接頂点の一致である（Berger–Fresse §1.1）。
方針：一致した二頂点の片方を除去した単体を逆像に取る。
規約：像の単体の次数は q+1。
使われ方：非退化単体を具体的な置換列で特徴づける。 -/
lemma mem_range_σ_iff (n q : ℕ) (x : (simplicial n) _⦋q + 1⦌)
    (i : Fin (q + 1)) :
    x ∈ Set.range ((simplicial n).σ i) ↔
      simplexEquiv n (q + 1) x i.castSucc = simplexEquiv n (q + 1) x i.succ := by
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro h
    refine ⟨(simplicial n).δ i.castSucc x, ?_⟩
    apply (simplexEquiv n (q + 1)).injective
    funext j
    simp only [simplexEquiv_σ, simplexEquiv_δ]
    by_cases h₁ : i.castSucc < j
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
      rw [Fin.predAbove_of_castSucc_lt _ _ h₁, Fin.pred_succ,
        Fin.succAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 h₁)]
    · simp only [not_lt] at h₁
      grind [→ Fin.succAbove_of_castSucc_lt,
        → Fin.predAbove_of_le_castSucc, Fin.castSucc_castPred, Fin.castPred_castSucc,
        Fin.succAbove_castSucc_self, → LE.le.lt_or_eq]

/-- 概要：非退化単体は隣接頂点が常に異なる置換列である（Berger–Fresse §1.1）。
方針：退化集合を全ての退化写像の像の和として記述する。
規約：0 単体に対しても空の条件として成立する。
使われ方：正規化鎖の基底の添字集合を与える。 -/
lemma mem_nonDegenerate_iff (n q : ℕ) (x : (simplicial n) _⦋q⦌) :
    x ∈ (simplicial n).nonDegenerate q ↔
      ∀ i : Fin q, simplexEquiv n q x i.castSucc ≠ simplexEquiv n q x i.succ := by
  cases q with
  | zero => simp
  | succ q =>
    simp only [SSet.nonDegenerate, Set.mem_compl_iff,
      SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion, mem_range_σ_iff, not_exists]

/-- 概要：右作用は非退化性を保存し反映する（Berger–Fresse §1.1）。
方針：隣接頂点の不一致に群の右消去則を適用する。
規約：任意の単体次数と置換についての同値。
使われ方：非退化単体集合に右作用を制限する。 -/
lemma rightAction_mem_nonDegenerate_iff (n q : ℕ) (σ : Equiv.Perm (Fin n))
    (x : (simplicial n) _⦋q⦌) :
    (rightAction n σ).app _ x ∈ (simplicial n).nonDegenerate q ↔
      x ∈ (simplicial n).nonDegenerate q := by
  simp only [mem_nonDegenerate_iff, simplexEquiv_rightAction]
  constructor
  · intro h i hi
    exact h i (congrArg (· * σ) hi)
  · intro h i hi
    exact h i (mul_right_cancel hi)

end SerrePositivity.EInfinity.BarrattEccles
