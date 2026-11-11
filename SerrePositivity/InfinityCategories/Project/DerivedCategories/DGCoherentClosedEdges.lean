module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentLowComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ coherent 閉射の実比較像の辺係数は、元の閉零成分。 -/
lemma dgCoherentComparison_closed_edgeHom (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) (f : x ⟶ y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge).edgeHom 0 1 (by decide) = (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D x y f).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_edgeHom]
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior
      (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) < ULift.up 1 from by decide) ∅) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath := Subsingleton.elim _ _
  rw [hp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) (D := D) x y 0
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' x y f) 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  have hE : SimplicialCategory.homEquiv' x y f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := R) (D := D) x y f := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y).unitHomEquiv
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y).unitHomEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := R) (D := D) x y f)) = _
    exact Equiv.apply_symm_apply _ _
  rw [hE]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval (R := R) x y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := R) (D := D) x y f)).val = _
  exact congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) x y).apply_symm_apply
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D x y f))
/-- 同じ coherent 閉射の実比較像は、元の同じ dg 閉射の実辺と厳密に一致する。 -/
lemma dgCoherentComparison_closed_edge (x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R D) (f : x ⟶ y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D))).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R D f).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact dgCoherentComparison_closed_edgeHom R D x y f
end SerrePositivity.InfinityCategories.Project.DerivedCategories
