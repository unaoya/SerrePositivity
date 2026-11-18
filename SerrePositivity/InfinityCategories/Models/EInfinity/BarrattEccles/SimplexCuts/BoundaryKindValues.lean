module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryPartition

/-!
模型。文献の定義との比較は後で
# 境界種類の端点と内部での評価

Berger–Fresse §2.2.7、M14 L09a。
有限な分類の定義を、後続の辺の挿入・削除の添字と同じ形で評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C51：始点の種類は最初の辺の向き。 -/
lemma boundaryVertexKind_zero {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (hN : 0 < m + q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s 0 =
      if (⟨0, hN⟩ : Fin (m + q)) ∈ s.val then .horizontal else .vertical := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind, hN]

/-- C52：終点の種類は最後の辺の向き。 -/
lemma boundaryVertexKind_last {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (hN : 0 < m + q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s (Fin.last (m + q)) =
      if (⟨m + q - 1, by omega⟩ : Fin (m + q)) ∈ s.val then .horizontal else .vertical := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind, dite_eq_left hN, Fin.val_last,
    dite_eq_right (Nat.ne_of_gt hN), dite_true]

/-- C53：内部頂点の種類は、その前後の二辺の向き。 -/
lemma boundaryVertexKind_interior {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1))
    (h : 0 < k.val ∧ k.val < m + q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k =
      if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerLeftEdge k h ∈ s.val then
        if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge k h ∈ s.val then .horizontal else .mixed
      else if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge k h ∈ s.val then .mixed else .vertical := by
  have hN : 0 < m + q := lt_trans h.1 h.2
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind
  rw [dite_eq_left hN, dite_eq_right (Nat.ne_of_gt h.1), dite_eq_right (ne_of_lt h.2)]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
