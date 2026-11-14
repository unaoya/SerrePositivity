module

public import SerrePositivity.EInfinity.SimplexCuts.NestedCompositeMap
public import SerrePositivity.EInfinity.SimplexCuts.CompositeOuterCut

/-!
# 同じ二段切断の元の外側切断の復元

Berger–Fresse §2.2.6、M14 L12a の逆の等式の証明分割。
指定した元の外側境界の高さと元のCutの単射な座標を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C435：合成切断を復元して射影すると元の外側切断に戻る（BF §2.2.6）。 -/
lemma positiveNestedCompositeMap_outerCut {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    positiveCompositeOuterCut u v k (positiveNestedCompositeMap u v k c) = c.1 := by
  apply cutHeights_injective
  apply OrderHom.ext
  funext i
  rw [positiveCompositeOuterCut_heights]
  exact positiveNestedCompositeMap_heights u v k c (Sum.inl i)

end SerrePositivity.EInfinity.SimplexCuts
