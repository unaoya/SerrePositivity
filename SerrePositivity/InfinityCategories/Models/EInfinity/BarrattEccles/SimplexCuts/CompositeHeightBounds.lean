module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeOuterCut

/-!
模型。文献の定義との比較は後で
# 元の合成切断の内部の辺の高さの範囲

Berger–Fresse §2.2.6、M14 L12a の内側射影の証明分割。
同じ接頭境界に挟まれた水平辺の高さを、射影した外側区間の両端で抑える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C409：元の合成語の区間内の高さは、射影した同じ外側区間内（BF §2.2.6）。 -/
lemma positiveCompositeOuterCut_height_bounds {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (a : Fin (m + n + (d + e)))
    (hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 p.val ≤ a.val)
    (hr : a.val + 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (p.val + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) p ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2 a).val ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2 a).val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) p := by
  constructor
  · by_cases hp : p.val = 0
    · have he : p = 0 := Fin.ext hp
      rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_zero]
      exact Nat.zero_le _
    · let i : Fin (m + d) := ⟨p.val - 1, by have h := p.isLt; omega⟩
      have he : p = i.succ := Fin.ext (by dsimp only [i]; simp only [Fin.val_succ]; omega)
      rw [he, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_lo_succ]
      change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) i).val ≤ _
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut_heights]
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2).monotone
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (i.val + 1) - 1 ≤ a.val
      have hv : i.val + 1 = p.val := by dsimp only [i]; omega
      rw [hv]
      omega
  · by_cases hp : p.val = m + d
    · have he : p = Fin.last (m + d) := Fin.ext hp
      rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_last]
      exact Nat.le_of_lt_succ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2 a).isLt
    · let i : Fin (m + d) := ⟨p.val, by have h := p.isLt; omega⟩
      have he : p = i.castSucc := Fin.ext rfl
      rw [he]
      change _ ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) i).val
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut_heights]
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2).monotone
      change a.val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (i.val + 1) - 1
      change a.val + 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (i.val + 1) at hr
      omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
