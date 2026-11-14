module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePrefixLengths
public import SerrePositivity.EInfinity.SimplexCuts.PositiveCompositeCuts
public import SerrePositivity.EInfinity.SimplexCuts.CutOfHeights

/-!
# 合成切断からの元の外側切断の射影

Berger–Fresse §2.2.6、M14 L12a。
元の外側区間の境界における合成切断の高さを、そのまま元のCutへ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C392：同じ合成切断の外側区間の境界での高さによる、元の外側切断（BF §2.2.6）。 -/
def positiveCompositeOuterCut {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveCompositeCutIndex u v k q) : Cut (m + d) q :=
  cutOfHeights ((cutHeights c.2).comp
    ⟨compositeOuterEdge u v k c.1, (compositeOuterEdge_strictMono u v k c.1).monotone⟩)

/-- C393：射影した元の外側切断は、指定した同じ境界の高さを持つ（BF §2.2.6）。 -/
lemma positiveCompositeOuterCut_heights {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveCompositeCutIndex u v k q) (i : Fin (m + d)) :
    cutHeights (positiveCompositeOuterCut u v k c) i =
      cutHeights c.2 (compositeOuterEdge u v k c.1 i) := by
  unfold positiveCompositeOuterCut
  exact congrArg (fun h : Fin (m + d) →o Fin (q + 1) => h i) (cutHeights_cutOfHeights _)

end SerrePositivity.EInfinity.SimplexCuts
