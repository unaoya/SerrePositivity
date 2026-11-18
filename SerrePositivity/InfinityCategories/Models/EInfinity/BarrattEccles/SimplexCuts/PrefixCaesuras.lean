module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VertexLists
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesuras

/-!
模型。文献の定義との比較は後で
# 接頭部と末尾に分けた caesura

Berger–Fresse §1.2.2・§2.2.4、M14 L09a C04。
接頭語で最後になった文字も、元の語の末尾に再出現すればcaesuraのままである。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 接頭語の位置を元の語へ戻す。 -/
def prefixPosition {m : ℕ} (p : Fin (m + 1)) (i : Fin (p.val + 1)) :
    Fin (m + 1) :=
  ⟨i.val, by have hi := i.isLt; have hp := p.isLt; omega⟩

/-- C04。後続の同色を、接頭部内と末尾へ分ける。 -/
lemma caesura_prefix_iff {m r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (i : Fin (p.val + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixPosition p i) ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixLabels v p) i ∨
      ∃ j : Fin (m + 1), p < j ∧ v j = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixLabels v p i := by
  constructor
  · rintro ⟨j, hij, hj⟩
    by_cases hpj : j ≤ p
    · left
      let k : Fin (p.val + 1) := ⟨j.val, by change j.val ≤ p.val at hpj; omega⟩
      exact ⟨k, hij, hj⟩
    · exact Or.inr ⟨j, lt_of_not_ge hpj, hj⟩
  · rintro (⟨j, hij, hj⟩ | ⟨j, hpj, hj⟩)
    · exact ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixPosition p j, hij, hj⟩
    · refine ⟨j, ?_, hj⟩
      have hi := i.isLt
      change p.val < j.val at hpj
      change i.val < j.val
      omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
