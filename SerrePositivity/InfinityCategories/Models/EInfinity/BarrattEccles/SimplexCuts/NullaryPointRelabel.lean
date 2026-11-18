module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointVertexLists
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OrderedColorEmbeddings

/-!
模型。文献の定義との比較は後で
# 削除後の同じ色づけへの元の符号と全頂点列の移送

Berger–Fresse §2.2.4・§2.2.6、M14 L12a、報告 §333。
残る色を指定色を飛ばす元の順序単射で戻し、同じ整数符号と全頂点列を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同じ削除色の番号を詰め直しても元の整数符号と一致する（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_cutSign_relabel {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : Fin (m + 2) → Fin (r + 1)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1))
    (hpoint : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p) (hu : ∀ j, v j = v p → j = p)
    (hv : ∀ i, k.succAbove (w i) = v (p.succAbove i)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s v := by
  have he : k.succAbove ∘ w = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p := funext hv
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) (k.succAbove ∘ w) :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign_comp_strictMono _ w k.succAbove (Fin.strictMono_succAbove k)).symm
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p) := by rw [he]
    _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign_erase_unique_point s v p hpoint hu

/-- 同じ削除後の色の全頂点列は元の残り色の全頂点列（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_verticesList_relabel {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : Fin (m + 2) → Fin (r + 1)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v p = k)
    (hpoint : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p)
    (hv : ∀ i, k.succAbove (w i) = v (p.succAbove i)) (c : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w c = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList s v (k.succAbove c) := by
  have he : k.succAbove ∘ w = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p := funext hv
  have hc : v p ≠ k.succAbove c := by
    rw [hp]
    exact (Fin.succAbove_ne k c).symm
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) (k.succAbove ∘ w) (k.succAbove c) :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList_comp_injective _ w k.succAbove
        (Fin.strictMono_succAbove k).injective c).symm
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v p) (k.succAbove c) := by
      rw [he]
    _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_verticesList_remaining s p hpoint v (k.succAbove c) hc

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
