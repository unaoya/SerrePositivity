module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedVertices

/-!
模型。文献の定義との比較は後で
# 順序付きfiberの順位

Berger–Fresse §2.2.7、M14 L09a。
昇順同値の添字を、それより前にある同色の頂点数と照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C29：昇順同値の添字は、より小さいfiberの元の数。 -/
lemma card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α] (t : Finset α) {N : ℕ}
    (h : t.card = N) (j : Fin N) :
    (t.filter (fun x => x < t.orderEmbOfFin h j)).card = j.val := by
  rw [← Fin.card_Iio j]
  symm
  apply Finset.card_bij (fun i _ => t.orderEmbOfFin h i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨t.orderEmbOfFin_mem h i,
      (t.orderEmbOfFin h).strictMono (Finset.mem_Iio.mp hi)⟩
  · intro i _ k _ hik
    exact (t.orderEmbOfFin h).injective hik
  · intro x hx
    let i := (t.orderIsoOfFin h).symm ⟨x, (Finset.mem_filter.mp hx).1⟩
    have he : t.orderEmbOfFin h i = x :=
      congrArg Subtype.val ((t.orderIsoOfFin h).apply_symm_apply ⟨x, (Finset.mem_filter.mp hx).1⟩)
    refine ⟨i, Finset.mem_Iio.mpr ?_, he⟩
    exact (t.orderEmbOfFin h).lt_iff_lt.mp (he ▸ (Finset.mem_filter.mp hx).2)

/-- C30：色の面番号の値は、その経路の頂点より前の同色の数。 -/
lemma colorPositionEquiv_rank {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a).filter (fun k => k < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u ⟨a, j⟩)).card =
      j.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv_apply]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.card_filter_lt_orderEmbOfFin _ _ j

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
