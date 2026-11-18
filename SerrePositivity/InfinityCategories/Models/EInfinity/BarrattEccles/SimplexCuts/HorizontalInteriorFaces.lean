module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalEndpointFaces
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalCorner

/-!
模型。文献の定義との比較は後で
# 内部の水平境界と小さい切断の水平辺

Berger–Fresse §2.2.7、M14 L09a。
連続する水平辺の中間頂点を削除する対応を、既存の角の挿入の同値から構成する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 内部の水平境界頂点。 -/
abbrev HorizontalInteriorFace (m q : ℕ) :=
  {t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut (m + 1) q // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .horizontal ∧
    0 < t.2.val ∧ t.2.val < m + 1 + q}

/-- 角の中間頂点の添字。 -/
def horizontalCornerVertex {m q : ℕ} (c : _root_.SerrePositivity.EInfinity.BarrattEccles.HorizontalCorner m q) :
    Fin (m + 1 + q + 1) := ⟨c.val.2.val + 1, by have h := c.val.2.isLt; omega⟩

/-- C67：二つの水平辺の角を、その中間の水平境界頂点へ移す。 -/
def horizontalCornerFaceEquiv (m q : ℕ) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.HorizontalCorner m q ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalInteriorFace m q where
  toFun c := by
    let k := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalCornerVertex c
    have hk : 0 < k.val ∧ k.val < m + 1 + q := by
      have h := c.val.2.isLt
      change 0 < c.val.2.val + 1 ∧ c.val.2.val + 1 < m + 1 + q
      omega
    refine ⟨⟨c.val.1, k⟩, ?_, hk⟩
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_horizontal_iff]
    refine ⟨by omega, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalVertex_interior_iff c.val.1 k hk).mpr ?_⟩
    have hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerLeftEdge k hk =
        Fin.cast (by omega : m + q + 1 = m + 1 + q) c.val.2.castSucc := by
      apply Fin.ext
      change c.val.2.val + 1 - 1 = c.val.2.val
      omega
    have hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge k hk =
        Fin.cast (by omega : m + q + 1 = m + 1 + q) c.val.2.succ := Fin.ext rfl
    rw [hl, hr]
    exact c.property
  invFun t := by
    let a : Fin (m + q) := ⟨t.val.2.val - 1, by have h := t.property.2; omega⟩
    refine ⟨(t.val.1, a), ?_⟩
    have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_horizontal_iff t.val.1 t.val.2).mp t.property.1
    have hh := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalVertex_interior_iff t.val.1 t.val.2 t.property.2).mp h.2
    have hl : Fin.cast (by omega : m + q + 1 = m + 1 + q) a.castSucc =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerLeftEdge t.val.2 t.property.2 := Fin.ext rfl
    have hr : Fin.cast (by omega : m + q + 1 = m + 1 + q) a.succ =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge t.val.2 t.property.2 := by
      apply Fin.ext
      change t.val.2.val - 1 + 1 = t.val.2.val
      have ht := t.property.2.1
      omega
    rw [hl, hr]
    exact hh
  left_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change c.val.2.val + 1 - 1 = c.val.2.val
      omega
  right_inv t := by
    apply Subtype.ext
    rcases t with ⟨⟨s, k⟩, h⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      change k.val - 1 + 1 = k.val
      have hk := h.2.1
      change 0 < k.val at hk
      omega

/-- C68：内部の水平面は、小さい切断と消す内部の区間番号で添字づけられる。 -/
def horizontalInteriorFaceEquiv (m q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q × Fin m ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalInteriorFace m q :=
  ((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalMarkedEdgeEquiv m q).trans
    (_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalCornerEquiv m q)).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalCornerFaceEquiv m q)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
