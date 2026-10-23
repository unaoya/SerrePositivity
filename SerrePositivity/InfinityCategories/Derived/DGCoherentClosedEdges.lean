module
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentLowComparison
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv
/-!
概要：coherent nerve の同じ閉射の比較像を、元の dg nerve の同じ閉射へ同定する。
方針：唯一の二点 path を標準 path に揃え、閉零元と標準零単体の同じ同値を評価する。
規約：辺そのものの厳密な一致。使われ方：実 coslice 輸送の同じ底の辺への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DoldKanComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 同じ coherent 閉射の実比較像の辺係数は、元の閉零成分。 -/
lemma dgCoherentComparison_closed_edgeHom (x y : ClosedCategory R D) (f : x ⟶ y) :
    ((coherentComparison (R := R) (D := D)).app (Opposite.op ⦋1⦌)
      (coherentNerveEdge f).edge).edgeHom 0 1 (by decide) = (closedHomEquiv R D x y f).val := by
  rw [coherentComparison_edgeHom]
  have hp : (Coherent.pathOfInterior
      (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) < ULift.up 1 from by decide) ∅) =
      coherentOnePath := Subsingleton.elim _ _
  rw [hp]
  change standardTopEval (R := R) (D := D) x y 0
    (PinchedHom.constant (SimplicialCategory.homEquiv' x y f) 0) = _
  rw [pinchedConstant_zero]
  have hE : SimplicialCategory.homEquiv' x y f =
      closedStandardVertexEquiv (R := R) (D := D) x y f := by
    change (standardHomSpace (R := R) (D := D) x y).unitHomEquiv
      ((standardHomSpace (R := R) (D := D) x y).unitHomEquiv.symm
        (closedStandardVertexEquiv (R := R) (D := D) x y f)) = _
    exact Equiv.apply_symm_apply _ _
  rw [hE]
  change (standardZeroEval (R := R) x y
    (closedStandardVertexEquiv (R := R) (D := D) x y f)).val = _
  exact congrArg Subtype.val ((standardZeroEquiv (R := R) (D := D) x y).apply_symm_apply
    (closedHomEquiv R D x y f))
/-- 同じ coherent 閉射の実比較像は、元の同じ dg 閉射の実辺と厳密に一致する。 -/
lemma dgCoherentComparison_closed_edge (x y : ClosedCategory R D) (f : x ⟶ y) :
    ((coherentNerveEdge f).map (coherentComparison (R := R) (D := D))).edge =
      (dgClosedEdge R D f).edge := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact dgCoherentComparison_closed_edgeHom R D x y f
end SerrePositivity.InfinityCategories
