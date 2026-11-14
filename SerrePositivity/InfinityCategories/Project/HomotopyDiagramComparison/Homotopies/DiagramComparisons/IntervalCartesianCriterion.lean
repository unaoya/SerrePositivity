module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IntervalCocartesianCriterion
/-!
概要：区間上の inner fibration の Cartesian 性を、非退化辺の持ち上げで判定する。
方針：区間の辺を恒等射と定値辺に分類し、定値辺には終点の恒等辺を使う。
規約：元の終点と底射影を厳密に保持する。使われ方：Quillen cf 対応圏の区間射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
/-- 非退化な区間辺の全終点での Cartesian lift から、区間上の Cartesian fibration を得る。 -/
lemma cartesianFibration_interval_of_lift {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [Quasicategory E] [InnerFibration p]
    (h : ∀ x : E _⦋0⦌, p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (1 : Fin 2) →
      ∃ l : (Δ[1] : SSet.{u}) ⟶ E,
        stdSimplex.δ 0 ≫ l = SSet.yonedaEquiv.symm x ∧ l ≫ p = 𝟙 Δ[1] ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv l)) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p := by
  constructor
  refine ⟨InnerFibration.mem, ?_⟩
  intro x e he
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.interval_hom_eq_id_or_const e with rfl | ⟨i, rfl⟩
  · apply h x
    apply SSet.yonedaEquiv.symm.injective
    rw [Category.comp_id, stdSimplex.δ_zero_eq_const,
      ← SSet.yonedaEquiv_symm_zero] at he
    exact he.symm
  · have hx : p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm i := by
      apply SSet.yonedaEquiv.symm.injective
      simpa only [SSet.comp_const, SSet.yonedaEquiv_symm_zero] using he.symm
    refine ⟨SSet.const x, ?_, ?_, ?_⟩
    · rw [SSet.comp_const, SSet.yonedaEquiv_symm_zero]
    · rw [SSet.const_comp, hx]
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)
      have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
          (SSet.Truncated.Edge.id (X := (truncation 2).obj E) x) := by
        change IsIso (SSet.Truncated.HomotopyCategory.homMk
          (SSet.Truncated.Edge.id (X := (truncation 2).obj E) x))
        rw [SSet.Truncated.HomotopyCategory.homMk_id]
        infer_instance
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge p _ hi

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
