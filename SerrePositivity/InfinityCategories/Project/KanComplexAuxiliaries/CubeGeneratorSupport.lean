module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActiveSupport
public import Mathlib.Order.Fin.Basic

/-! # 立方体の生成射の有効入力と順序
概要：各生成射の有効入力を元の Fin 座標から判定し、出力順に並ぶことを証明する。
方針：挿入・削除では座標の埋め込み、max では隣接する二座標の範囲を使う。
規約：右端から数える座標の順序を保持する。使われ方：具体的な cubical 射の support。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 恒等射の有効入力は同じ座標。 -/
lemma cubeActive_id {n : ℕ} {i j : Fin n}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) i j) : j = i := by
  simpa [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] using h.2

/-- 面の有効入力は、挿入した座標を飛ばす元の座標。 -/
lemma cubeActive_face {n : ℕ} {b : Bool} {p j : Fin (n + 1)} {i : Fin n}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n p) i j) : j = p.succAbove i := by
  refine Fin.succAboveCases p ?_ (fun k => ?_) j h
  · intro hp
    have hzero : b = false := by simpa [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace] using hp.1
    have hone : b = true := by simpa [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace] using hp.2
    exact Bool.noConfusion (hzero.symm.trans hone)
  · intro hk
    have heq : k = i := by simpa [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] using hk.2
    exact congrArg p.succAbove heq

/-- 退化の有効入力は、削除した座標を飛ばす元の座標。 -/
lemma cubeActive_degeneracy {n : ℕ} {p i : Fin (n + 1)} {j : Fin n}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n p) i j) : p.succAbove j = i := by
  simpa [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] using h.2

/-- max の有効入力は、結合座標では二座標、他では元の一座標。 -/
lemma cubeActive_connection {n : ℕ} {p j : Fin (n + 1)} {i : Fin (n + 2)}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n p) i j) :
    (j = p ∧ (p.castSucc = i ∨ p.succ = i)) ∨
      (j ≠ p ∧ p.succ.succAbove j = i) := by
  by_cases hj : j = p
  · left
    refine ⟨hj, ?_⟩
    subst j
    have hi := h.2
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, Function.update_self, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] at hi
    by_cases hleft : p.castSucc = i
    · exact Or.inl hleft
    · right
      simpa [hleft] using hi
  · right
    refine ⟨hj, ?_⟩
    simpa [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, Function.update_of_ne hj, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom] using h.2

/-- 恒等射の有効入力は出力順に並ぶ。 -/
lemma cubeSupportOrdered_id (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) := by
  intro j k hjk i l hi hl
  rwa [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_id hi, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_id hl] at hjk

/-- 面の有効入力は出力順に並ぶ。 -/
lemma cubeSupportOrdered_face (b : Bool) (n : ℕ) (p : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n p) := by
  intro j k hjk i l hi hl
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_face hi, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_face hl] at hjk
  exact (Fin.strictMono_succAbove p).lt_iff_lt.mp hjk

/-- 退化の有効入力は出力順に並ぶ。 -/
lemma cubeSupportOrdered_degeneracy (n : ℕ) (p : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n p) := by
  intro j k hjk i l hi hl
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_degeneracy hi, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_degeneracy hl]
  exact Fin.strictMono_succAbove p hjk

/-- max の有効入力の番号は、元の出力の番号またはその次の番号。 -/
lemma cubeActive_connection_bounds {n : ℕ} {p j : Fin (n + 1)} {i : Fin (n + 2)}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeActive (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n p) i j) :
    j.val + (if p.val < j.val then 1 else 0) ≤ i.val ∧
      i.val ≤ j.val + (if p.val ≤ j.val then 1 else 0) := by
  obtain ⟨rfl, h | h⟩ | ⟨hjp, h⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_connection h
  · subst i
    simp
  · subst i
    simp
  · have hpj : p.val ≠ j.val := fun h => hjp (Fin.ext h.symm)
    rw [← h]
    simp only [Fin.succAbove]
    split <;> simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      <;> split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> omega

/-- max の有効入力は、隣接二座標の範囲も含めて出力順に並ぶ。 -/
lemma cubeSupportOrdered_connection (n : ℕ) (p : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportOrdered (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n p) := by
  intro j k hjk i l hi hl
  obtain ⟨_, hi⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_connection_bounds hi
  obtain ⟨hl, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_connection_bounds hl
  have hjk' : j.val < k.val := hjk
  change i.val < l.val
  split_ifs at hi hl <;> omega

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeActive_connection := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_connection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeActive_connection_bounds := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_connection_bounds

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeActive_degeneracy := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_degeneracy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeActive_face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeActive_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeActive_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOrdered_connection := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_connection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOrdered_degeneracy := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_degeneracy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOrdered_face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOrdered_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOrdered_id
