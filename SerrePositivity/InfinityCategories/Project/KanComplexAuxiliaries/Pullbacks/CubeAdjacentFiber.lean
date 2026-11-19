module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Pullbacks.CubeFiberMax

/-! # 隣接二座標を同一視する fiber max と元の connection
概要：Fin.predAbove の fiber max が、元の隣接 max connection そのものと一致する。
方針：片方の座標を飛ばす二つの埋め込みを比較し、各 fiber の真の入力を回収する。
規約：元の右端からの座標順を保つ。使われ方：一般の単調全射の次元帰納。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 隣接する二点を飛ばす埋め込みは、その二点の間の出力以外で一致する。 -/
lemma cubeAdjacent_succAbove_eq {n : ℕ} (p j : Fin (n + 1)) (hj : j ≠ p) :
    p.castSucc.succAbove j = p.succ.succAbove j := by
  have hval : j.val ≠ p.val := fun h => hj (Fin.ext h)
  apply Fin.ext
  simp only [Fin.succAbove]
  split_ifs <;> simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;> omega

/-- 同一視した座標の fiber は元の隣接二点、他の fiber は元の一座標。 -/
lemma cubeAdjacent_fiber_true_iff {n : ℕ} (p : Fin (n + 1))
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 2)) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax p.predAbove x j = true ↔
      (j = p ∧ x p.castSucc = true) ∨ x (p.castSucc.succAbove j) = true := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff]
  constructor
  · rintro ⟨i, hi, hx⟩
    by_cases hp : i = p.castSucc
    · subst i
      exact Or.inl ⟨(Fin.predAbove_castSucc_self p).symm.trans hi |>.symm, hx⟩
    · right
      rw [← hi, Fin.succAbove_predAbove hp]
      exact hx
  · rintro (⟨rfl, hx⟩ | hx)
    · exact ⟨j.castSucc, Fin.predAbove_castSucc_self j, hx⟩
    · exact ⟨p.castSucc.succAbove j, Fin.predAbove_succAbove p j, hx⟩

/-- 隣接座標の同一視の fiber max は、元の具体的な max connection。 -/
lemma cubeFiberMax_predAbove (n : ℕ) (p : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax p.predAbove = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n p := by
  funext x j
  apply Bool.eq_iff_iff.mpr
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeAdjacent_fiber_true_iff]
  by_cases hj : j = p
  · subst j
    simp only [Fin.succAbove_castSucc_self, true_and, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection,
      Function.update_self]
    cases hx : x p.castSucc <;> cases hy : x p.succ <;> simp_all
  · simp only [hj, false_and, false_or]
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeAdjacent_succAbove_eq p j hj]
    simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, hj, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
