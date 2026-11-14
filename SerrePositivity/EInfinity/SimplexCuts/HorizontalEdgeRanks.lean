module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointCuts

/-!
# 元の水平座標から読む同じ水平辺の昇順番号

Berger–Fresse §1.1.3・§2.2.6、M14 L12a の既存構成の法則、報告 §321。
元の同じ辺集合の昇順番号と指定挿入位置を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の水平座標を指定すると、所属水平辺の昇順番号はその値（BF §1.1.3）。 -/
lemma cutHorizontalEdge_eq_of_horizontal {m q : ℕ} (s : Cut m q)
    (a : Fin (m + q)) (ha : a ∈ s.val) (i : Fin m)
    (hi : s.horizontal a.castSucc = i.castSucc) : cutHorizontalEdge s i = a := by
  let e := s.val.orderIsoOfFin s.property
  let j := e.symm ⟨a, ha⟩
  have he : cutHorizontalEdge s j = a := congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
  have hj := horizontal_before_cutHorizontalEdge s j
  rw [he, hi] at hj
  have hij : i = j := Fin.ext (congrArg (fun z : Fin (m + 1) => z.val) hj)
  rw [hij]
  exact he

end SerrePositivity.EInfinity.SimplexCuts
