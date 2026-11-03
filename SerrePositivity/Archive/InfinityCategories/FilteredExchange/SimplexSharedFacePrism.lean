module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SimplexFaceVertexGeometry

/-!
概要：同じ実単体の隣接面で共有される実部分図式を一致させる。
方針：標準単体の二重面関係を全係数との積と実全図式の制限へ移す。
規約：比較用の新たな充填を選ばない。使われ方：四面体の六本の共有辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 隣接する実面の共有部分は、全係数を保って同じ実図式になる。 -/
lemma simplexSharedFacePrism {n : ℕ} {E P : SSet.{u}}
    (W : (Δ[n + 2] : SSet.{u}) ⊗ P ⟶ E) (i j : Fin (n + 2)) (hij : i ≤ j) :
    (stdSimplex.δ j ▷ P) ≫ ((stdSimplex.δ i.castSucc ▷ P) ≫ W) =
      (stdSimplex.δ i ▷ P) ≫ ((stdSimplex.δ j.succ ▷ P) ≫ W) := by
  rw [← Category.assoc, ← Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight]
  rw [stdSimplex.δ_comp_δ hij]

end SerrePositivity.InfinityCategories.F2
