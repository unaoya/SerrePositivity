module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma rightFibration_liftEdge_target {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (x : E _⦋0⦌) {y : B _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj B)
      y (p.app (Opposite.op ⦋0⦌) x)) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ E,
      stdSimplex.δ 0 ≫ F = SSet.yonedaEquiv.symm x ∧
        F ≫ p = SSet.yonedaEquiv.symm e.edge := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro (1 : Fin 2) (by decide))
  have sq : CommSq (SSet.const x) (horn 1 1).ι p (SSet.yonedaEquiv.symm e.edge) := by
    constructor
    apply horn.hom_ext'
    intro j hj
    fin_cases j
    · rw [SSet.const_comp, SSet.comp_const, horn.ι_ι_assoc,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact (SSet.yonedaEquiv_symm_zero _).symm.trans
        (congrArg SSet.yonedaEquiv.symm e.tgt_eq.symm)
    · exact (hj rfl).elim
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  rw [← horn.ι_ι_assoc 1 0 (by decide), sq.fac_left, SSet.comp_const,
    SSet.yonedaEquiv_symm_zero]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
