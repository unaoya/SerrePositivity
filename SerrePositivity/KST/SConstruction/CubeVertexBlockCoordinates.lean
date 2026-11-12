module
public import SerrePositivity.KST.SConstruction.CubeVertexBlocks

/-! # 元の cube 連結の数値座標
概要：右から数える元の再帰的 cubeVertexJoin を、全数値座標で回収する。
方針：右ブロックの長さで帰納し、元の Fin.cons の評価を使う。
規約：右ブロックが先。使われ方：necklace の元の右端列挙との厳密な照合。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の連結の左座標は、右の長さだけ後ろに置かれる。 -/
lemma cubeVertexJoin_left_coordinate {n m : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
    (i : Fin n) : cubeVertexJoin x y ⟨m + i.val, by have := i.isLt; omega⟩ = x i := by
  induction m with
  | zero =>
    change x ⟨0 + i.val, _⟩ = x i
    congr 1
    apply Fin.ext
    change 0 + i.val = i.val
    omega
  | succ m ih =>
    have he : (⟨m + 1 + i.val, by have := i.isLt; omega⟩ : Fin (n + (m + 1))) =
        (⟨m + i.val, by have := i.isLt; omega⟩ : Fin (n + m)).succ := Fin.ext (by
          change m + 1 + i.val = (m + i.val) + 1
          omega)
    rw [he]
    exact ih (fun j => y j.succ)

/-- 元の連結の右座標は、零から同じ番号で始まる。 -/
lemma cubeVertexJoin_right_coordinate {n m : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
    (i : Fin m) : cubeVertexJoin x y ⟨i.val, by have := i.isLt; omega⟩ = y i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change cubeVertexJoin x (fun k => y k.succ) ⟨j.val, _⟩ = y j.succ
      exact ih (fun k => y k.succ) j

end SerrePositivity.KST.SConstruction
