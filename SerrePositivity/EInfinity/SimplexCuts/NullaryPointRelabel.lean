module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointSigns
public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointVertexLists
public import SerrePositivity.EInfinity.SimplexCuts.OrderedColorEmbeddings

/-!
# 削除後の同じ色づけへの元の符号と全頂点列の移送

Berger–Fresse §2.2.4・§2.2.6、M14 L12a、報告 §333。
残る色を指定色を飛ばす元の順序単射で戻し、同じ整数符号と全頂点列を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ削除色の番号を詰め直しても元の整数符号と一致する（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_cutSign_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin (r + 1)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1))
    (hpoint : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p)
    (hv : ∀ i, k.succAbove (w i) = v (p.succAbove i)) :
    cutSign (nullaryPointEraseCut s p) w = cutSign s v := by
  have he : k.succAbove ∘ w = Surjection.erase v p := funext hv
  calc
    _ = cutSign (nullaryPointEraseCut s p) (k.succAbove ∘ w) :=
      (cutSign_comp_strictMono _ w k.succAbove (Fin.strictMono_succAbove k)).symm
    _ = cutSign (nullaryPointEraseCut s p) (Surjection.erase v p) := by rw [he]
    _ = _ := cutSign_erase_unique_point s v p hpoint hu

/-- 同じ削除後の色の全頂点列は元の残り色の全頂点列（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_verticesList_relabel {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin (r + 1)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v p = k)
    (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w i) = v (p.succAbove i)) (c : Fin r) :
    verticesList (nullaryPointEraseCut s p) w c = verticesList s v (k.succAbove c) := by
  have he : k.succAbove ∘ w = Surjection.erase v p := funext hv
  have hc : v p ≠ k.succAbove c := by
    rw [hp]
    exact (Fin.succAbove_ne k c).symm
  calc
    _ = verticesList (nullaryPointEraseCut s p) (k.succAbove ∘ w) (k.succAbove c) :=
      (verticesList_comp_injective _ w k.succAbove
        (Fin.strictMono_succAbove k).injective c).symm
    _ = verticesList (nullaryPointEraseCut s p) (Surjection.erase v p) (k.succAbove c) := by
      rw [he]
    _ = _ := nullaryPointEraseCut_verticesList_remaining s p hpoint v (k.succAbove c) hc

end SerrePositivity.EInfinity.SimplexCuts
