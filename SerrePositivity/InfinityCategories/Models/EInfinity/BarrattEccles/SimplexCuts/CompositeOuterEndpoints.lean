module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeBlockPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeOuterCut

/-!
模型。文献の定義との比較は後で
# 同じ合成語のブロック両端と元の外側区間の高さ

Berger–Fresse §2.2.6、M14 L12a の指定面の照合。
同じ接頭境界の高さを左右の元の区間の両端として読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C451c・C451d：同じ外側区間の両端は元の合成ブロックの両端（BF §2.2.6）。 -/
lemma positiveCompositeOuterCut_endpoints {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) (p : Fin (m + d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k c.1 p) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeLastPosition u v k c.1 p) := by
  constructor
  · by_cases hp : p.val = 0
    · have he : p = 0 := Fin.ext hp
      have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k c.1 p = 0 := by
        apply Fin.ext
        change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 p.val = 0
        rw [hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength_zero]
      rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_zero, ← he, hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_zero]
    · let i : Fin (m + d) := ⟨p.val - 1, by have h := p.isLt; omega⟩
      have hipos : i.val + 1 = p.val := by dsimp only [i]; omega
      have he : p = i.succ := Fin.ext hipos.symm
      have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength_step u v k c.1
        (⟨i.val, by have h := i.isLt; omega⟩ : Fin ((m + 1) + d))
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 i.val + 1 ≤
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (i.val + 1) at hs
      have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k c.1 p =
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeOuterEdge u v k c.1 i).succ := by
        apply Fin.ext
        change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 p.val =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (i.val + 1) - 1 + 1
        rw [hipos] at hs ⊢
        omega
      calc
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) p =
            _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) i.castSucc := by rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_lo_succ]
        _ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeOuterEdge u v k c.1 i)).val :=
          congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut_heights u v k c i)
        _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k c.1 p) := by
          rw [hf, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_lo_succ]
          rfl
  · by_cases hp : p.val = m + d
    · have he : p = Fin.last (m + d) := Fin.ext hp
      have hfull : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (p.val + 1) = m + (n + 1) + (d + e) := by
        have hv : p.val + 1 = (m + 1) + d := by omega
        rw [hv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength_full]
      have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeLastPosition u v k c.1 p = Fin.last (m + n + (d + e)) := by
        apply Fin.ext
        change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (p.val + 1) - 1 = m + n + (d + e)
        rw [hfull]
        omega
      rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_last, ← he, hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_last]
    · let i : Fin (m + d) := ⟨p.val, by have h := p.isLt; omega⟩
      have he : p = i.castSucc := Fin.ext rfl
      have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeLastPosition u v k c.1 p =
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeOuterEdge u v k c.1 i).castSucc := rfl
      calc
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) p =
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) i).val := by rw [he]; rfl
        _ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeOuterEdge u v k c.1 i)).val :=
          congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut_heights u v k c i)
        _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeLastPosition u v k c.1 p) := by rw [hf]; rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
