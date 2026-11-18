module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.WeightedColorPairs
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.WeightedVertexInversions

/-!
模型。文献の定義との比較は後で
# 一般の切断の色置換と BF 符号

Berger–Fresse §2.2.4、M14 L11 の証明分割。
色置換で活動位置と位置指数は不変、隣接交換の符号は両出力次数の積で変わる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C321：元の展開色列の色置換は、同じ経路での後合成（BF §2.2.4）。 -/
lemma label_rename {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (σ : Equiv.Perm (Fin r)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s (σ ∘ v) = σ ∘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v := rfl

/-- C322：色置換は同じ活動頂点集合を保つ（BF §2.2.4）。 -/
lemma activeVertexPositions_rename {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (σ : Equiv.Perm (Fin r)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s (σ ∘ v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v := by
  ext k
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (σ ∘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_rename_iff σ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k

/-- C323：色置換は同じ内側右端点の位置指数を保つ（BF §2.2.4）。 -/
lemma positionExponent_rename {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (σ : Equiv.Perm (Fin r)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s (σ ∘ v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_rename_iff]

/-- C320：隣接色交換の切断符号の変化は、一般の二出力次数の Koszul 符号（BF §2.2.4）。 -/
lemma cutSign_adjacent {m q n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (n + 1) (m + 1)) (a : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s (_root_.SerrePositivity.Coxeter.adjacentTransposition a ∘ v.val) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s v.val * (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a.castSucc * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a.succ) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign, pow_add, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.permutationExponent_eq_active_inversions,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent_rename, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions_rename, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label_rename,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionInversionSign_adjacent_weighted, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.active_color_card]
  ring

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
