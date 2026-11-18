module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointNormalization

/-!
模型。文献の定義との比較は後で
# 残り色の番号を詰め直した元の正規化零項

Berger–Fresse §2.2.6、M14 L12a、報告 §335。
元のpairの第一成分の単射だけを使って非退化性を両方向へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 色の単射は元の正規化零項を保つ（BF §2.2.6）。 -/
lemma nondegenerate_comp_injective {m q r R : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (φ : Fin r → Fin R) (hφ : Function.Injective φ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s (φ ∘ v) ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s v := by
  constructor
  · intro h i j hij
    have hx := congrArg (fun z : Fin r × Fin (q + 1) => z.1) hij
    have hy := congrArg (fun z : Fin r × Fin (q + 1) => z.2) hij
    apply h
    exact Prod.ext (congrArg φ hx) hy
  · intro h i j hij
    have hx := congrArg (fun z : Fin R × Fin (q + 1) => z.1) hij
    have hy := congrArg (fun z : Fin R × Fin (q + 1) => z.2) hij
    apply h
    exact Prod.ext (hφ hx) hy

/-- 同じ削除後の色の番号へ移しても元の非退化性と同値（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_nondegenerate_relabel {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : Fin (m + 2) → Fin (r + 1)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1))
    (hpoint : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p) (hu : ∀ j, v j = v p → j = p)
    (hv : ∀ i, k.succAbove (w i) = v (p.succAbove i)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s v := by
  have he : k.succAbove ∘ w = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p := funext hv
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nondegenerate_comp_injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w k.succAbove
    (Fin.strictMono_succAbove k).injective, he]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_nondegenerate_iff s v p hpoint hu

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
