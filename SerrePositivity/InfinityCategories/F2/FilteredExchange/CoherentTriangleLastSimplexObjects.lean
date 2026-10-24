module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleLastInitialHead
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ThickeningSelfHomComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SimplicialHomDisplayComposition
/-!
概要：最大化側の最後辺と元の二射の係数作用の実単体を同じ対象表示で比較する。
方針：元の初点固定 tail と、第一射を作用させた全係数に続く最後射の tail を使う。
規約：元の全次数の係数を保持する。
使われ方：Ncomp の実 prism の対象・head・tail の一致。
-/

@[expose] public section
open CategoryTheory SSet SimplicialThickening MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
noncomputable section
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (s : SpaceInfinity.{u} _⦋2⦌)
/-- 概要：最大化側の最後辺の同じ全係数の実単体。方針：元の二時刻のラベルを保持する。
規約：全初点係数を保持。使われ方：元の実単体の比較。 -/
def coherentTriangleLastSourceSimplex {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌) :
    SpaceInfinity.{u} _⦋n + 1⦌ :=
  coneInitialFixedSimplex pointKanObject (coherentTriangleLastTail s α) (SSet.yonedaEquiv.symm p)
/-- 概要：第一射を作用させた全係数に続く元の最後射の実単体。方針：元の二時刻のラベルを保持する。
規約：全初点係数を保持。使われ方：元の実単体の比較。 -/
def coherentTriangleLastCompositeSimplex {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌) :
    SpaceInfinity.{u} _⦋n + 1⦌ :=
  coneInitialFixedSimplex pointKanObject
    (morphismInitialTail (coherentEdgeHom (SpaceInfinity.δ 0 s)) α)
    (SSet.yonedaEquiv.symm ((SSet.opFunctor.map
      (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s)))).app
        (Opposite.op ⦋n⦌) p))
/-- 概要：両方の実単体の対象は全頂点で一致。方針：元の二時刻のラベルを保持する。
規約：全初点係数を保持。使われ方：元の実単体の比較。 -/
lemma coherentTriangleLastSimplex_obj {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌)
    (a : Fin (n + 2)) :
    (coherentTriangleLastSourceSimplex s α p).obj ⟨ULift.up a⟩ =
      (coherentTriangleLastCompositeSimplex s α p).obj ⟨ULift.up a⟩ := by
  induction a using Fin.cases with
  | zero => rfl
  | succ j =>
    change (coherentTriangleLastTail s α).val.obj ⟨ULift.up j.succ⟩ =
      (morphismInitialTail (coherentEdgeHom (SpaceInfinity.δ 0 s)) α).val.obj ⟨ULift.up j.succ⟩
    have ht : α.toOrderHom j = 0 ∨ α.toOrderHom j = 1 :=
      (by decide : ∀ z : Fin 2, z = 0 ∨ z = 1) _
    rcases ht with hj | hj
    · exact (coherentTriangleLastTail_obj_zero s α j hj).trans
        (morphismInitialTail_obj_zero (coherentEdgeHom (SpaceInfinity.δ 0 s)) α j hj).symm
    · exact (coherentTriangleLastTail_obj_one s α j hj).trans
        (morphismInitialTail_obj_one (coherentEdgeHom (SpaceInfinity.δ 0 s)) α j hj).symm
end SerrePositivity.InfinityCategories.F2
