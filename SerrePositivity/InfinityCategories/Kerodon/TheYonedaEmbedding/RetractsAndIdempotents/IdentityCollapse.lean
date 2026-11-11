module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking

/-!
概要：隣接する恒等射を潰す元の順序自己写像を、nerve の退化の判定に使う。
方針：元の余面と退化の合成を恒等への順序射で比較する。
規約：元の単体と同じ nerve の退化作用を保持する。
使われ方：非退化な分裂添字の単体の隣接射の分類。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の i+1 位置だけを元の i 位置へ潰す順序自己写像。 -/
def identityCollapse {n : ℕ} (i : Fin (n + 1)) : Fin (n + 2) →o Fin (n + 2) :=
  (Fin.succAboveOrderEmb i.succ).toOrderHom.comp (Fin.predAboveOrderHom i)

/-- 指定した元の位置は、その元の直前の位置へ潰れる。 -/
lemma identityCollapse_succ {n : ℕ} (i : Fin (n + 1)) :
    identityCollapse i i.succ = i.castSucc := by
  simp [identityCollapse]

/-- 指定位置以外の元の位置は固定される。 -/
lemma identityCollapse_of_ne {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : j ≠ i.succ) : identityCollapse i j = j :=
  Fin.succ_succAbove_predAbove h

/-- 元の潰す写像から元の恒等への、元の有限順序の比較。 -/
lemma identityCollapse_le {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    identityCollapse i j ≤ j := by
  by_cases h : j = i.succ
  · subst j
    rw [identityCollapse_succ]
    exact i.castSucc_le_succ
  · rw [identityCollapse_of_ne i j h]

/-- 元の潰す順序写像に沿った前合成から、元の全単体への自然変換。 -/
def identityCollapseComparison {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} (n + 1)) :
    (identityCollapse i).monotone.functor ⋙ F ⟶ F where
  app j := F.map (homOfLE (identityCollapse_le i j))
  naturality {j k} f := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    congr 1

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
