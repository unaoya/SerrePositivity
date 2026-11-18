module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositePartitionRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NestedCutRightInverse

/-!
模型。文献の定義との比較は後で
# 元の一段切断と二段切断の全有限添字の対応

Berger–Fresse §2.2.6、M14 L12a の正の有限対応。
元の分割と全水平辺の高さを保ち、両方向が厳密に逆であることを組み立てる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C450：二段切断へ射影してから復元すると、元の同じ合成切断へ戻る（BF §2.2.6）。 -/
lemma positiveCompositeNestedMap_leftInverse {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) :
    Function.LeftInverse (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedCompositeMap u v k (q := q))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap u v k) := by
  intro c
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap_partition u v k c
  apply Prod.ext hr
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights_injective
  apply OrderHom.ext
  funext i
  obtain ⟨z, hz⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeEdgeSum_bijective u v k c.1).2 i
  rw [← hz]
  have hh := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedCompositeMap_heights u v k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap u v k c) z
  rw [hr] at hh
  rw [hh]
  cases z with
  | inl a => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut_heights u v k c a
  | inr a => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut_vertices u v k c a

/-- 正の全ての元の有限切断添字の対応。退化した切断も保持する（BF §2.2.6）。 -/
def positiveCompositeNestedEquiv {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCutIndex u v k q where
  toFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap u v k
  invFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedCompositeMap u v k
  left_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap_leftInverse u v k
  right_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap_rightInverse u v k

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
