module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OrderedPrefixCard
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalBoundaryGlue

/-!
模型。文献の定義との比較は後で
# 元の切断の水平辺の高さ

Berger–Fresse §2.2.3–6、M14 L12a の経路の復元。
元の右端点hiと元の水平辺の昇順列挙の座標を合わせる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の第i水平辺の位置の記法（BF §2.2.3）。 -/
abbrev cutHorizontalEdge {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin m) : Fin (m + q) :=
  s.val.orderEmbOfFin s.property i

/-- 元の切断の第i水平辺の高さを、元のhiで読む（BF §2.2.3）。 -/
def cutHeights {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) : Fin m →o Fin (q + 1) where
  toFun i := ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i.castSucc, Nat.lt_succ_of_le (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_le_q s i.castSucc)⟩
  monotone' i j hij := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_monotone s (show i.castSucc ≤ j.castSucc from hij)

/-- C378：元の第i水平辺の直前の水平座標はi（BF §2.2.3）。 -/
lemma horizontal_before_cutHorizontalEdge {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin m) :
    s.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i).castSucc = i.castSucc := by
  apply Fin.ext
  change (s.val.filter (fun j => j.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i).val)).card = i.val
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.card_filter_lt_orderEmbOfFin s.val s.property i

/-- C380：同じ水平辺の直前の垂直座標は元の区間の右端点（BF §2.2.3）。 -/
lemma vertical_before_cutHorizontalEdge {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin m) :
    (s.vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i).castSucc).val = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s i).val := by
  change _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i.castSucc
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_before_cutHorizontalEdge s i,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.interval_max_before_horizontal s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i) (s.val.orderEmbOfFin_mem s.property i)]

/-- C379：元の水平辺の位置は、その番号と高さの和（BF §2.2.3）。 -/
lemma cutHorizontalEdge_val {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i).val = i.val + (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s i).val := by
  have h := s.coordinate_sum (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i).castSucc
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_before_cutHorizontalEdge] at h
  change i.val + (s.vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i).castSucc).val =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i).val at h
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_before_cutHorizontalEdge] at h
  exact h.symm

/-- C381：元の水平辺の高さは、元の切断自体を決定する（BF §2.2.3）。 -/
lemma cutHeights_injective {m q : ℕ} : Function.Injective (@_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights m q) := by
  intro s t h
  have he : ∀ i : Fin m, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge t i := by
    intro i
    apply Fin.ext
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge_val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge_val]
    exact congrArg (fun f : Fin m →o Fin (q + 1) => i.val + (f i).val) h
  apply Subtype.ext
  calc
    s.val = Finset.univ.image (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s) :=
      (Finset.image_orderEmbOfFin_univ s.val s.property).symm
    _ = Finset.univ.image (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge t) :=
      congrArg (fun f : Fin m → Fin (m + q) => Finset.univ.image f) (funext he)
    _ = t.val := Finset.image_orderEmbOfFin_univ t.val t.property

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
