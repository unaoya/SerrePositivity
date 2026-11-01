module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Zigzag
public import Lean.Elab.Tactic.Omega

/-!
# 語の連続部分への向きを保つ包含

概要：一定の番号差で埋め込まれる語の連続部分を構成する。
方針：列と頂点を同じ自然数だけずらし、向きと区間を照合する。
規約：空語も含め、単射を filtered 性の仮定には使わない。
使われ方：連結の左右の部分の同方向区間の比較。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Hammock.Word

/-- 元の語の連続部分としての、向きを保つ包含。 -/
structure Block (a b : Word) where
  offset : ℕ
  bound : offset + a.length ≤ b.length
  direction_eq : ∀ i : Fin a.length,
    b.direction ⟨offset + i.val, by have := i.isLt; omega⟩ = a.direction i

namespace Block
variable {a b : Word}

def column (B : Block a b) (i : Fin a.length) : Fin b.length :=
  ⟨B.offset + i.val, by have := B.bound; have := i.isLt; omega⟩

def vertex (B : Block a b) (i : Fin (a.length + 1)) : Fin (b.length + 1) :=
  ⟨B.offset + i.val, by have := B.bound; have := i.isLt; omega⟩

lemma vertex_monotone (B : Block a b) : Monotone B.vertex :=
  fun _ _ h => Nat.add_le_add_left h _

lemma vertex_sub (B : Block a b) (p q : Fin (a.length + 1)) :
    (B.vertex q).val - (B.vertex p).val = q.val - p.val := by
  dsimp [vertex]
  omega

lemma source_eq (B : Block a b) (i : Fin a.length) :
    b.source (B.column i) = B.vertex (a.source i) := by
  unfold Word.source
  rw [show b.direction (B.column i) = a.direction i from B.direction_eq i]
  cases a.direction i <;> rfl

lemma target_eq (B : Block a b) (i : Fin a.length) :
    b.target (B.column i) = B.vertex (a.target i) := by
  unfold Word.target
  rw [show b.direction (B.column i) = a.direction i from B.direction_eq i]
  cases a.direction i <;> rfl

/-- 元の同方向区間は、連続部分への包含に沿っても同じ方向。 -/
lemma interval_direction (B : Block a b) (d : Direction) (p q : Fin (a.length + 1))
    (hd : ∀ j : Fin a.length, p.val ≤ j.val → j.val < q.val → a.direction j = d)
    (i : Fin b.length) (hi : (B.vertex p).val ≤ i.val) (hi' : i.val < (B.vertex q).val) :
    b.direction i = d := by
  have hq := q.isLt
  change B.offset + p.val ≤ i.val at hi
  change i.val < B.offset + q.val at hi'
  let j : Fin a.length := ⟨i.val - B.offset, by omega⟩
  have hji : B.column j = i := Fin.ext (by dsimp [column, j]; omega)
  exact (congrArg b.direction hji).symm.trans
    ((B.direction_eq j).trans (hd j (by dsimp [j]; omega) (by dsimp [j]; omega)))

end Block
end SerrePositivity.EInfinity.Hammock.Word
