module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointCuts

/-!
# nullaryの元の挿入辺の三位置の値

Berger–Fresse §1.1.3・§2.2.6、M14 L12a の既存構成の法則、報告 §321。
元の同じ辺集合の昇順番号と指定挿入位置を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 始点の同じ挿入辺は零番（BF §2.2.6）。 -/
lemma nullaryPointInsertionEdge_first {m q : ℕ} (t : Cut m q) :
    nullaryPointInsertionEdge t 0 = 0 := rfl

/-- 終点の同じ挿入辺は最後の辺（BF §2.2.6）。 -/
lemma nullaryPointInsertionEdge_last {m q : ℕ} (t : Cut m q) :
    nullaryPointInsertionEdge t (Fin.last (m + 1)) = (⟨m + q, by omega⟩ : Fin (m + 1 + q)) := by
  unfold nullaryPointInsertionEdge
  split
  · next hzero =>
      have hbad : m + 1 = 0 := hzero
      omega
  · split
    · rfl
    · next htop => exact False.elim (htop rfl)

/-- 内部の同じ挿入辺は、指定水平辺の直後（BF §2.2.6）。 -/
lemma nullaryPointInsertionEdge_interior {m q : ℕ} (t : Cut m q) (i : Fin m) :
    nullaryPointInsertionEdge t i.castSucc.succ =
      Fin.cast (by omega) (cutHorizontalEdge t i).succ := by
  unfold nullaryPointInsertionEdge
  split
  · next hzero =>
      have hbad : i.val + 1 = 0 := hzero
      omega
  · split
    · next htop =>
        have hbad : i.val + 1 = m + 1 := htop
        have hi := i.isLt
        omega
    · apply Fin.ext
      simp only [Fin.val_cast, Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel]

end SerrePositivity.EInfinity.SimplexCuts
