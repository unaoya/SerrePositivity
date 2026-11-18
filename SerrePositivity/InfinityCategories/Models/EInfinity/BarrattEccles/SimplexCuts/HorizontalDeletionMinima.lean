module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalValidTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedIntervalMinima

/-!
模型。文献の定義との比較は後で
# 水平削除の指定座標から左端と色列を読む

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
既存の水平削除の座標対応を、区間の左端と同じ削除列へ移す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 左端の法則：水平削除の指定座標は、残る区間の左端を保つ。 -/
lemma lo_eq_of_horizontal_deleted_coordinates {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hh : ∀ j : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) =
        a.succAbove (t.horizontal j))
    (hv : ∀ j : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j)) = t.vertical j)
    (i : Fin (m + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo t i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s (a.succAbove i) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_eq_of_coordinate_cover s t
    (fun j => k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) j))
    a.succAbove (Fin.strictMono_succAbove a).injective hh hv i
  intro j hj
  have hne : j ≠ k := by
    intro he
    rw [he, hk] at hj
    exact Fin.succAbove_ne a i hj.symm
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hne
  refine ⟨Fin.cast (by omega : m + 1 + q = m + q + 1) l, ?_⟩
  have hc : Fin.cast (by omega : m + q + 1 = m + 1 + q)
      (Fin.cast (by omega : m + 1 + q = m + q + 1) l) = l := Fin.ext rfl
  change k.succAbove (Fin.cast _ (Fin.cast _ l)) = j
  rw [hc]
  exact hl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
