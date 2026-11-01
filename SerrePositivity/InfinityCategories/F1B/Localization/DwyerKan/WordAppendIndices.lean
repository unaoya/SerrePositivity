module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordAppend
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Zigzag

/-!
# 連結語の元の列と頂点の位置

概要：連結語の左右の全頂点と、元の向き付き列の両端の位置を照合する。
方針：列は有限順序の直和、頂点は共有する接合点を含めて番号を移す。
規約：左の終点と右の始点は同じ頂点番号となる。
使われ方：固定端点 zigzag の連結と遷移の自然性。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Hammock.Word

/-- 連結語の左の部分の全頂点。 -/
def leftVertex (a b : Word) (i : Fin (a.length + 1)) : Fin ((append a b).length + 1) :=
  ⟨i.val, by have := i.isLt; dsimp [append]; omega⟩

/-- 連結語の右の部分の全頂点。 -/
def rightVertex (a b : Word) (i : Fin (b.length + 1)) : Fin ((append a b).length + 1) :=
  ⟨a.length + i.val, by have := i.isLt; dsimp [append]; omega⟩

@[simp] lemma leftVertex_zero (a b : Word) : leftVertex a b 0 = 0 := rfl

@[simp] lemma rightVertex_last (a b : Word) :
    rightVertex a b (Fin.last b.length) = Fin.last (append a b).length := rfl

lemma jointVertex (a b : Word) : leftVertex a b (Fin.last a.length) = rightVertex a b 0 := rfl

lemma source_left (a b : Word) (i : Fin a.length) :
    (append a b).source (i.castAdd b.length) = leftVertex a b (a.source i) := by
  unfold source
  rw [append_direction_left]
  cases a.direction i <;> rfl

lemma target_left (a b : Word) (i : Fin a.length) :
    (append a b).target (i.castAdd b.length) = leftVertex a b (a.target i) := by
  unfold target
  rw [append_direction_left]
  cases a.direction i <;> rfl

lemma source_right (a b : Word) (i : Fin b.length) :
    (append a b).source (i.natAdd a.length) = rightVertex a b (b.source i) := by
  unfold source
  rw [append_direction_right]
  cases b.direction i <;> rfl

lemma target_right (a b : Word) (i : Fin b.length) :
    (append a b).target (i.natAdd a.length) = rightVertex a b (b.target i) := by
  unfold target
  rw [append_direction_right]
  cases b.direction i <;> rfl

end SerrePositivity.EInfinity.Hammock.Word
