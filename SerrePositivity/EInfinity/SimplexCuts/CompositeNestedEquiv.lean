module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePartitionRecovery
public import SerrePositivity.EInfinity.SimplexCuts.NestedCutRightInverse

/-!
# 元の一段切断と二段切断の全有限添字の対応

Berger–Fresse §2.2.6、M14 L12a の正の有限対応。
元の分割と全水平辺の高さを保ち、両方向が厳密に逆であることを組み立てる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C450：二段切断へ射影してから復元すると、元の同じ合成切断へ戻る（BF §2.2.6）。 -/
lemma positiveCompositeNestedMap_leftInverse {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) :
    Function.LeftInverse (positiveNestedCompositeMap u v k (q := q))
      (positiveCompositeNestedMap u v k) := by
  intro c
  have hr := positiveCompositeNestedMap_partition u v k c
  apply Prod.ext hr
  apply cutHeights_injective
  apply OrderHom.ext
  funext i
  obtain ⟨z, hz⟩ := (compositeEdgeSum_bijective u v k c.1).2 i
  rw [← hz]
  have hh := positiveNestedCompositeMap_heights u v k (positiveCompositeNestedMap u v k c) z
  rw [hr] at hh
  rw [hh]
  cases z with
  | inl a => exact positiveCompositeOuterCut_heights u v k c a
  | inr a => exact positiveCompositeInnerCut_vertices u v k c a

/-- 正の全ての元の有限切断添字の対応。退化した切断も保持する（BF §2.2.6）。 -/
def positiveCompositeNestedEquiv {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    PositiveCompositeCutIndex u v k q ≃ PositiveNestedCutIndex u v k q where
  toFun := positiveCompositeNestedMap u v k
  invFun := positiveNestedCompositeMap u v k
  left_inv := positiveCompositeNestedMap_leftInverse u v k
  right_inv := positiveCompositeNestedMap_rightInverse u v k

end SerrePositivity.EInfinity.SimplexCuts
