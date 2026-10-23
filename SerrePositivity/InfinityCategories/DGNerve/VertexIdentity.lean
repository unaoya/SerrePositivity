module
public import SerrePositivity.InfinityCategories.DGNerve.EdgeHomotopy

/-! # dg nerve の頂点の恒等辺

augmentation の二系統で同一だった一般計算を、型と証明を保って直接移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial

/-- 実 dg 頂点の恒等辺は、同じ実単位から構成した一単体。 -/
lemma dgNerve_vertex_identity_simplex (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
    (X : C) :
    (SSet.Truncated.Edge.id (X := (truncation 2).obj (dgNerve R C))
      (Simplex.vertex X)).edge = Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X) := by
  have he := edgeOfCycle_edgeCycle
    (SSet.Truncated.Edge.id (X := (truncation 2).obj (dgNerve R C)) (Simplex.vertex X))
  rw [edgeCycle_id] at he
  have hh := congrArg (fun e ↦ e.edge) he
  have hobj : pairObj X X = (fun _ : Fin 2 ↦ X) := by
    funext i
    fin_cases i <;> rfl
  change Simplex.ofEdge (pairObj X X) (unitElement R X) = _ at hh
  have ho : Simplex.ofEdge (pairObj X X) (unitElement R X) =
      Simplex.ofEdge (fun _ : Fin 2 ↦ X) (unitElement R X) := by
    apply Simplex.edgeEquiv.injective
    exact Sigma.ext hobj (heq_of_eq rfl)
  exact hh.symm.trans ho
end SerrePositivity.InfinityCategories
