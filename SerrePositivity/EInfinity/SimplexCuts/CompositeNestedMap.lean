module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeInnerHeights

/-!
# 元の一段切断から二段切断への順方向

Berger–Fresse §2.2.6、M14 L12a。
元の外側切断と同じ頂点列の元の内側切断を組にする。逆写像や符号はここで仮定しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ高さから元のCutを読む内側切断（BF §2.2.6）。 -/
def positiveCompositeInnerCut {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Cut (n + e) (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k) :=
  cutOfHeights (positiveCompositeInnerHeights u v k c)

/-- C415：元の内側切断は指定した同じ高さを保つ（BF §2.2.6）。 -/
lemma positiveCompositeInnerCut_heights {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    cutHeights (positiveCompositeInnerCut u v k c) a = positiveCompositeInnerHeights u v k c a :=
  congrArg (fun h : Fin (n + e) →o
    Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1) => h a)
      (cutHeights_cutOfHeights (positiveCompositeInnerHeights u v k c))

/-- C416：元の色別頂点写像で読むと、同じ合成切断の高さと一致（BF §2.2.6）。 -/
lemma positiveCompositeInnerCut_vertices {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (cutHeights (positiveCompositeInnerCut u v k c) a) =
      cutHeights c.2 (compositeInnerEdge u v k c.1 a) := by
  rw [positiveCompositeInnerCut_heights]
  apply Fin.ext
  exact vertices_colorHeightRank (positiveCompositeOuterCut u v k c) (positiveWord u) k
    (positiveOccurrencePosition u k
      (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val))
    (positiveOccurrencePosition_value u k _)
    (cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val
    (positiveCompositeInnerEdge_height_bounds u v k c a).1
    (positiveCompositeInnerEdge_height_bounds u v k c a).2

/-- 元の全ての正の合成切断から、その元の二段切断への写像（BF §2.2.6）。 -/
def positiveCompositeNestedMap {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) : PositiveCompositeCutIndex u v k q → PositiveNestedCutIndex u v k q :=
  fun c => ⟨positiveCompositeOuterCut u v k c, positiveCompositeInnerCut u v k c⟩

/-- C417：元の二段切断の外側は指定した同じ射影（BF §2.2.6）。 -/
lemma positiveCompositeNestedMap_outer {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    (positiveCompositeNestedMap u v k c).1 = positiveCompositeOuterCut u v k c := rfl

end SerrePositivity.EInfinity.SimplexCuts
