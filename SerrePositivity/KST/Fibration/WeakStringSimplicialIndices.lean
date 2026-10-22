module
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison

/-! # 面による連続辺の合成と退化による恒等辺の挿入の元の添字 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.KST.Fibration

/-- 元の長い列の三つの連続頂点を選ぶ二単体。 -/
def consecutiveWeakStringTriangle (n : ℕ) (i : Fin (n + 1)) : ⦋2⦌ ⟶ ⦋n + 2⦌ :=
  SimplexCategory.Hom.mk {
    toFun := fun j => ⟨i.val + j.val, by
      have hj : j.val < 3 := j.isLt
      change i.val + j.val < n + 3
      omega⟩
    monotone' := fun _ _ h => Nat.add_le_add_left h _ }

/-- 選んだ二単体の第一短辺は、元の同じ添字の連続辺。 -/
lemma consecutiveWeakStringTriangle_first (n : ℕ) (i : Fin (n + 1)) :
    SimplexCategory.δ (2 : Fin 3) ≫ consecutiveWeakStringTriangle n i =
      consecutiveWeakStringEdge (n + 2) i.castSucc := by
  ext j
  fin_cases j <;> rfl

/-- 選んだ二単体の第二短辺は、元の次の連続辺。 -/
lemma consecutiveWeakStringTriangle_second (n : ℕ) (i : Fin (n + 1)) :
    SimplexCategory.δ (0 : Fin 3) ≫ consecutiveWeakStringTriangle n i =
      consecutiveWeakStringEdge (n + 2) i.succ := by
  ext j
  change i.val + ((0 : Fin 3).succAbove j).val = i.val + 1 + j.val
  simp [Fin.succAbove]
  omega

/-- 内部面で合成された実辺は、元の三連続頂点の二単体の長辺。 -/
lemma consecutiveWeakStringEdge_innerFace (n : ℕ) (i : Fin (n + 1)) :
    consecutiveWeakStringEdge (n + 1) i ≫ SimplexCategory.δ i.castSucc.succ =
      SimplexCategory.δ (1 : Fin 3) ≫ consecutiveWeakStringTriangle n i := by
  ext j
  have hj : j.val < 2 := j.isLt
  change (i.castSucc.succ.succAbove ⟨i.val + j.val, by omega⟩).val =
    i.val + ((1 : Fin 3).succAbove j).val
  fin_cases j <;> simp [Fin.succAbove, Fin.lt_def]

/-- 退化の繰り返し頂点の辺は、元の頂点の恒等辺である。 -/
lemma consecutiveWeakStringEdge_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    consecutiveWeakStringEdge (n + 1) i ≫ SimplexCategory.σ i =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ i := by
  ext j
  have hj : j.val < 2 := j.isLt
  change (i.predAbove ⟨i.val + j.val, by omega⟩).val = i.val
  fin_cases j <;> simp [Fin.predAbove, Fin.lt_def]

end SerrePositivity.KST.Fibration
