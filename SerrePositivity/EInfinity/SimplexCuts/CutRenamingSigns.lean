module

public import SerrePositivity.EInfinity.SimplexCuts.WeightedColorPairs
public import SerrePositivity.EInfinity.SimplexCuts.WeightedVertexInversions

/-!
# 一般の切断の色置換と BF 符号

Berger–Fresse §2.2.4、M14 L11 の証明分割。
色置換で活動位置と位置指数は不変、隣接交換の符号は両出力次数の積で変わる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C321：元の展開色列の色置換は、同じ経路での後合成（BF §2.2.4）。 -/
lemma label_rename {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (σ : Equiv.Perm (Fin r)) : label s (σ ∘ v) = σ ∘ label s v := rfl

/-- C322：色置換は同じ活動頂点集合を保つ（BF §2.2.4）。 -/
lemma activeVertexPositions_rename {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (σ : Equiv.Perm (Fin r)) :
    activeVertexPositions s (σ ∘ v) = activeVertexPositions s v := by
  ext k
  simp only [activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  change Surjection.Caesura (σ ∘ label s v) k ↔ Surjection.Caesura (label s v) k
  exact Surjection.caesura_rename_iff σ (label s v) k

/-- C323：色置換は同じ内側右端点の位置指数を保つ（BF §2.2.4）。 -/
lemma positionExponent_rename {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (σ : Equiv.Perm (Fin r)) :
    positionExponent s (σ ∘ v) = positionExponent s v := by
  simp only [positionExponent, Surjection.caesura_rename_iff]

/-- C320：隣接色交換の切断符号の変化は、一般の二出力次数の Koszul 符号（BF §2.2.4）。 -/
lemma cutSign_adjacent {m q n : ℕ} (s : Cut m q)
    (v : Surjection.Word (n + 1) (m + 1)) (a : Fin n) :
    cutSign s (Coxeter.adjacentTransposition a ∘ v.val) =
      cutSign s v.val * (-1 : ℤ) ^ (outputDegree s v a.castSucc * outputDegree s v a.succ) := by
  simp only [cutSign, pow_add, permutationExponent_eq_active_inversions,
    positionExponent_rename, activeVertexPositions_rename, label_rename,
    positionInversionSign_adjacent_weighted, active_color_card]
  ring

end SerrePositivity.EInfinity.SimplexCuts
