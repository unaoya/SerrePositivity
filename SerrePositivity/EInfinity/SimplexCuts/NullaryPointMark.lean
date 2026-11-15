module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointBoundaryComparison

/-!
# nullaryの元の挿入辺と同じ水平境界の指定頂点

Berger–Fresse §1.1.3・§2.2.6、M14 L12a の既存構成の法則、報告 §321。
始点・内部・終点の元の指定位置を自然数の値で厳密に照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ水平境界の指定頂点は、元の挿入辺の直前（終点では直後）（BF §2.2.6）。 -/
lemma nullaryPointInsertionEdge_mark_val {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    (horizontalBoundaryFaceEquiv m q (p, t)).val.2.val =
      (nullaryPointInsertionEdge t p).val + if p.val = m + 1 then 1 else 0 := by
  by_cases hzero : p.val = 0
  · have hp : p = 0 := Fin.ext hzero
    subst p
    rw [horizontalBoundaryFaceEquiv_first, nullaryPointInsertionEdge_first]
    change (0 : ℕ) = 0 + if (0 : ℕ) = m + 1 then 1 else 0
    rw [ite_eq_right (by omega : (0 : ℕ) ≠ m + 1)]
  by_cases hlast : p.val = m + 1
  · have hp : p = Fin.last (m + 1) := Fin.ext hlast
    subst p
    rw [horizontalBoundaryFaceEquiv_last, nullaryPointInsertionEdge_last]
    change m + 1 + q = (m + q) + if m + 1 = m + 1 then 1 else 0
    rw [ite_eq_left rfl]
    omega
  let i : Fin m := ⟨p.val - 1, by have hp := p.isLt; omega⟩
  have hp : p = i.castSucc.succ := by
    apply Fin.ext
    change p.val = (p.val - 1) + 1
    omega
  rw [hp, horizontalBoundaryFaceEquiv_interior, nullaryPointInsertionEdge_interior]
  change (cutHorizontalEdge t i).val + 1 =
    (cutHorizontalEdge t i).val + 1 + if i.val + 1 = m + 1 then 1 else 0
  rw [ite_eq_right (by have hi := i.isLt; omega : i.val + 1 ≠ m + 1)]

end SerrePositivity.EInfinity.SimplexCuts
