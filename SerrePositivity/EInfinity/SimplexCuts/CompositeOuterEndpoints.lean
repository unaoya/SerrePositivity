module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeBlockPositions
public import SerrePositivity.EInfinity.SimplexCuts.CompositeOuterCut

/-!
# 同じ合成語のブロック両端と元の外側区間の高さ

Berger–Fresse §2.2.6、M14 L12a の指定面の照合。
同じ接頭境界の高さを左右の元の区間の両端として読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C451c・C451d：同じ外側区間の両端は元の合成ブロックの両端（BF §2.2.6）。 -/
lemma positiveCompositeOuterCut_endpoints {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (p : Fin (m + d + 1)) :
    lo (positiveCompositeOuterCut u v k c) p = lo c.2 (compositeFirstPosition u v k c.1 p) ∧
      hi (positiveCompositeOuterCut u v k c) p = hi c.2 (compositeLastPosition u v k c.1 p) := by
  constructor
  · by_cases hp : p.val = 0
    · have he : p = 0 := Fin.ext hp
      have hf : compositeFirstPosition u v k c.1 p = 0 := by
        apply Fin.ext
        change compositePrefixLength u v k c.1 p.val = 0
        rw [hp, compositePrefixLength_zero]
      rw [he, lo_zero, ← he, hf, lo_zero]
    · let i : Fin (m + d) := ⟨p.val - 1, by have h := p.isLt; omega⟩
      have hipos : i.val + 1 = p.val := by dsimp only [i]; omega
      have he : p = i.succ := Fin.ext hipos.symm
      have hs := compositePrefixLength_step u v k c.1
        (⟨i.val, by have h := i.isLt; omega⟩ : Fin ((m + 1) + d))
      change compositePrefixLength u v k c.1 i.val + 1 ≤
        compositePrefixLength u v k c.1 (i.val + 1) at hs
      have hf : compositeFirstPosition u v k c.1 p =
          (compositeOuterEdge u v k c.1 i).succ := by
        apply Fin.ext
        change compositePrefixLength u v k c.1 p.val =
          compositePrefixLength u v k c.1 (i.val + 1) - 1 + 1
        rw [hipos] at hs ⊢
        omega
      calc
        lo (positiveCompositeOuterCut u v k c) p =
            hi (positiveCompositeOuterCut u v k c) i.castSucc := by rw [he, hi_eq_lo_succ]
        _ = (cutHeights c.2 (compositeOuterEdge u v k c.1 i)).val :=
          congrArg Fin.val (positiveCompositeOuterCut_heights u v k c i)
        _ = lo c.2 (compositeFirstPosition u v k c.1 p) := by
          rw [hf, ← hi_eq_lo_succ]
          rfl
  · by_cases hp : p.val = m + d
    · have he : p = Fin.last (m + d) := Fin.ext hp
      have hfull : compositePrefixLength u v k c.1 (p.val + 1) = m + (n + 1) + (d + e) := by
        have hv : p.val + 1 = (m + 1) + d := by omega
        rw [hv, compositePrefixLength_full]
      have hf : compositeLastPosition u v k c.1 p = Fin.last (m + n + (d + e)) := by
        apply Fin.ext
        change compositePrefixLength u v k c.1 (p.val + 1) - 1 = m + n + (d + e)
        rw [hfull]
        omega
      rw [he, hi_last, ← he, hf, hi_last]
    · let i : Fin (m + d) := ⟨p.val, by have h := p.isLt; omega⟩
      have he : p = i.castSucc := Fin.ext rfl
      have hf : compositeLastPosition u v k c.1 p =
          (compositeOuterEdge u v k c.1 i).castSucc := rfl
      calc
        hi (positiveCompositeOuterCut u v k c) p =
            (cutHeights (positiveCompositeOuterCut u v k c) i).val := by rw [he]; rfl
        _ = (cutHeights c.2 (compositeOuterEdge u v k c.1 i)).val :=
          congrArg Fin.val (positiveCompositeOuterCut_heights u v k c i)
        _ = hi c.2 (compositeLastPosition u v k c.1 p) := by rw [hf]; rfl

end SerrePositivity.EInfinity.SimplexCuts
