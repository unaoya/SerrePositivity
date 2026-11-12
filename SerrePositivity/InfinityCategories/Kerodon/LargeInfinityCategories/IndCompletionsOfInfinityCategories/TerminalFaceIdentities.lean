module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-!
概要：最後の頂点を保持する面と境界の最後の面の可換性。
方針：単体圏の面恒等式を標準単体とその境界に移す。
規約：頂点写像は標準単体の元の定値写像。
使われ方：最後の面の一意な延長から終対象性を導く。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 標準単体の最後の頂点の写像。 -/
def lastVertexMap (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))

/-- 最後の頂点以外を除く面は、最後の頂点を保持する。 -/
lemma lastVertexMap_face (n : ℕ) (i : Fin (n + 2)) :
    lastVertexMap (n + 1) ≫ stdSimplex.δ i.castSucc = lastVertexMap (n + 2) := by
  change stdSimplex.map _ ≫ stdSimplex.map _ = stdSimplex.map _
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  ext j
  simp [SimplexCategory.const, SimplexCategory.δ, Fin.succAbove, not_lt_of_ge (Fin.le_last i)]

/-- 境界内の最後の面とそれ以外の面の共通部分。 -/
lemma boundaryLastFace_comp (n : ℕ) (i : Fin (n + 2)) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ boundary.ι i.castSucc =
      stdSimplex.δ i ≫ boundary.ι (Fin.last (n + 2)) := by
  apply (cancel_mono (boundary (n + 2)).ι).mp
  simp only [Category.assoc, boundary.ι_ι]
  exact congrArg (fun f => stdSimplex.map f)
    (SimplexCategory.δ_comp_δ (i := i) (j := Fin.last (n + 1)) (Fin.le_last i)).symm

/-- 同じ面の最後の頂点は境界の最後の頂点。 -/
lemma lastVertexMap_boundaryFace (n : ℕ) (i : Fin (n + 2)) :
    lastVertexMap (n + 1) ≫ boundary.ι i.castSucc = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex (n + 1) (Fin.last (n + 2)) := by
  apply (cancel_mono (boundary (n + 2)).ι).mp
  rw [Category.assoc, boundary.ι_ι, lastVertexMap_face, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
