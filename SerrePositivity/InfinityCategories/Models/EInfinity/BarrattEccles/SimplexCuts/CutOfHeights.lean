module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutHeights

/-!
模型。文献の定義との比較は後で
# 同じ単調な高さから元の切断を組み立てる

Berger–Fresse §2.2.3–6、M14 L12a の経路復元。
元のShufflePathの有限集合の構成子へ、水平位置i+h_iの像を渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 単調な水平辺の高さが指定する元の辺番号（BF §2.2.3）。 -/
def heightPosition {m q : ℕ} (h : Fin m →o Fin (q + 1)) (i : Fin m) : Fin (m + q) :=
  ⟨i.val + (h i).val, by have hi := i.isLt; have hh := (h i).isLt; omega⟩

/-- C383：単調な高さから読む辺番号は厳密に増える（BF §2.2.3）。 -/
lemma heightPosition_strictMono {m q : ℕ} (h : Fin m →o Fin (q + 1)) :
    StrictMono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.heightPosition h) := by
  intro i j hij
  have hm := h.monotone hij.le
  change (h i).val ≤ (h j).val at hm
  change i.val + (h i).val < j.val + (h j).val
  have hij' : i.val < j.val := hij
  omega

/-- C382：同じ水平位置の像を、元の切断の有限集合へ渡す（BF §2.2.3）。 -/
def cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q :=
  ⟨Finset.univ.image (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.heightPosition h), by
    rw [Finset.card_image_of_injective _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.heightPosition_strictMono h).injective]
    simp⟩

/-- C384：構成した同じ水平辺の昇順列挙は、指定した辺番号（BF §2.2.3）。 -/
lemma cutHorizontalEdge_cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) (i : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutOfHeights h) i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.heightPosition h i := by
  have H := Finset.orderEmbOfFin_unique (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutOfHeights h).property
    (f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.heightPosition h) (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.heightPosition_strictMono h)
  exact (congrFun H i).symm

/-- C385：構成した元の切断は、指定した同じ水平辺の高さを持つ（BF §2.2.3）。 -/
lemma cutHeights_cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutOfHeights h) = h := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge_val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutOfHeights h) i
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge_cutOfHeights] at H
  change i.val + (h i).val = i.val + (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutOfHeights h) i).val at H
  omega

/-- C386：同じ元の高さから組み立て直すと、元の切断そのもの（BF §2.2.3）。 -/
lemma cutOfHeights_cutHeights {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutOfHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights_injective
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights_cutOfHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
