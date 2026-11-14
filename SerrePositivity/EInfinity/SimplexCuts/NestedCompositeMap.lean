module

public import SerrePositivity.EInfinity.SimplexCuts.NestedCompositeEdgeHeights
public import SerrePositivity.EInfinity.SimplexCuts.CutOfHeights

/-!
# 元の二段切断から元の合成切断への逆方向

Berger–Fresse §2.2.6、M14 L12a。
同じ全辺の列挙から元のCutを読む。両方向の逆の等式や符号はここで仮定しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の全合成辺を同じ列挙で読み、その元の高さを指定する（BF §2.2.6）。 -/
def positiveNestedCompositeHeights {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    Fin (m + n + (d + e)) →o Fin (q + 1) where
  toFun a := positiveNestedEdgeHeight u v k c
    ((compositeEdgeEquiv u v k (positiveNestedPartition u v k c)).symm a)
  monotone' := by
    intro a b hab
    apply positiveNestedEdgeHeight_mono
    change compositeEdgeEquiv u v k (positiveNestedPartition u v k c)
        ((compositeEdgeEquiv u v k (positiveNestedPartition u v k c)).symm a) ≤
      compositeEdgeEquiv u v k (positiveNestedPartition u v k c)
        ((compositeEdgeEquiv u v k (positiveNestedPartition u v k c)).symm b)
    simpa only [Equiv.apply_symm_apply] using hab

/-- C433：指定した元の辺位置の高さは、同じ二段切断の高さ（BF §2.2.6）。 -/
lemma positiveNestedCompositeHeights_apply {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q)
    (z : Fin (m + d) ⊕ Fin (n + e)) :
    positiveNestedCompositeHeights u v k c
        (compositeEdgeSum u v k (positiveNestedPartition u v k c) z) =
      positiveNestedEdgeHeight u v k c z := by
  change positiveNestedEdgeHeight u v k c
      ((compositeEdgeEquiv u v k (positiveNestedPartition u v k c)).symm
        (compositeEdgeEquiv u v k (positiveNestedPartition u v k c) z)) = _
  rw [Equiv.symm_apply_apply]

/-- 元の二段切断から、その同じ重なる分割と元の合成切断への写像（BF §2.2.6）。 -/
def positiveNestedCompositeMap {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) : PositiveNestedCutIndex u v k q → PositiveCompositeCutIndex u v k q :=
  fun c => ⟨positiveNestedPartition u v k c, cutOfHeights (positiveNestedCompositeHeights u v k c)⟩

/-- C434：復元した元の合成切断は、指定した同じ全辺の高さを保つ（BF §2.2.6）。 -/
lemma positiveNestedCompositeMap_heights {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q)
    (z : Fin (m + d) ⊕ Fin (n + e)) :
    cutHeights (positiveNestedCompositeMap u v k c).2
        (compositeEdgeSum u v k (positiveNestedPartition u v k c) z) =
      positiveNestedEdgeHeight u v k c z := by
  change cutHeights (cutOfHeights (positiveNestedCompositeHeights u v k c)) _ = _
  rw [cutHeights_cutOfHeights]
  exact positiveNestedCompositeHeights_apply u v k c z

end SerrePositivity.EInfinity.SimplexCuts
