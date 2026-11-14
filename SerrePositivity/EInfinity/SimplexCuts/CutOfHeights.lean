module

public import SerrePositivity.EInfinity.SimplexCuts.CutHeights

/-!
# 同じ単調な高さから元の切断を組み立てる

Berger–Fresse §2.2.3–6、M14 L12a の経路復元。
元のShufflePathの有限集合の構成子へ、水平位置i+h_iの像を渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 単調な水平辺の高さが指定する元の辺番号（BF §2.2.3）。 -/
def heightPosition {m q : ℕ} (h : Fin m →o Fin (q + 1)) (i : Fin m) : Fin (m + q) :=
  ⟨i.val + (h i).val, by have hi := i.isLt; have hh := (h i).isLt; omega⟩

/-- C383：単調な高さから読む辺番号は厳密に増える（BF §2.2.3）。 -/
lemma heightPosition_strictMono {m q : ℕ} (h : Fin m →o Fin (q + 1)) :
    StrictMono (heightPosition h) := by
  intro i j hij
  have hm := h.monotone hij.le
  change (h i).val ≤ (h j).val at hm
  change i.val + (h i).val < j.val + (h j).val
  have hij' : i.val < j.val := hij
  omega

/-- C382：同じ水平位置の像を、元の切断の有限集合へ渡す（BF §2.2.3）。 -/
def cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) : Cut m q :=
  ⟨Finset.univ.image (heightPosition h), by
    rw [Finset.card_image_of_injective _ (heightPosition_strictMono h).injective]
    simp⟩

/-- C384：構成した同じ水平辺の昇順列挙は、指定した辺番号（BF §2.2.3）。 -/
lemma cutHorizontalEdge_cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) (i : Fin m) :
    cutHorizontalEdge (cutOfHeights h) i = heightPosition h i := by
  have H := Finset.orderEmbOfFin_unique (cutOfHeights h).property
    (f := heightPosition h) (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    (heightPosition_strictMono h)
  exact (congrFun H i).symm

/-- C385：構成した元の切断は、指定した同じ水平辺の高さを持つ（BF §2.2.3）。 -/
lemma cutHeights_cutOfHeights {m q : ℕ} (h : Fin m →o Fin (q + 1)) :
    cutHeights (cutOfHeights h) = h := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  have H := cutHorizontalEdge_val (cutOfHeights h) i
  rw [cutHorizontalEdge_cutOfHeights] at H
  change i.val + (h i).val = i.val + (cutHeights (cutOfHeights h) i).val at H
  omega

/-- C386：同じ元の高さから組み立て直すと、元の切断そのもの（BF §2.2.3）。 -/
lemma cutOfHeights_cutHeights {m q : ℕ} (s : Cut m q) :
    cutOfHeights (cutHeights s) = s := by
  apply cutHeights_injective
  exact cutHeights_cutOfHeights (cutHeights s)

end SerrePositivity.EInfinity.SimplexCuts
