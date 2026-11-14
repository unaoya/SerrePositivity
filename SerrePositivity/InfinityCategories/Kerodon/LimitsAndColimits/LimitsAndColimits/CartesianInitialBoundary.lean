module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CartesianInitialBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cartesian fibration の fiber の始対象から全空間の相対始点境界充填を得る。
方針：反転した射に Core の cocartesian な輸送を供給し、既存の fiber の判定を使う。
規約：輸送の比較を明示的な定理とし、循環する instance は作らない。
使われ方：図式の制限の fiber の始対象性を全空間へ移す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：cartesian fibration を反転すると Core の cocartesian な輸送を持つ。
方針：反転した底の辺を元の終点指定の辺に戻し、その cartesian な持ち上げを反転する。
規約：底と全空間の quasicategory 性は不要。
使われ方：反転による fiber の始対象からの相対境界充填。 -/
lemma cartesianFibration_op_toCocartesianHornFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration (SSet.opFunctor.map p) where
  mem := InnerFibration.mem
  exists_lift x b a := by
    let a₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop a
    have ha : stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm a₀.edge =
        SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv x)) := by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm a₀.tgt_eq
    obtain ⟨f, hf, hfp, hfc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration.mem (p := p) |>.2 (SSet.opObjEquiv x) _ ha
    have ht : E.δ 0 (SSet.yonedaEquiv f) = SSet.opObjEquiv x := by
      rw [← stdSimplex.yonedaEquiv_δ_comp, hf, Equiv.apply_symm_apply]
    let e₀ : SSet.Truncated.Edge (X := (truncation 2).obj E)
        (E.δ 1 (SSet.yonedaEquiv f)) (SSet.opObjEquiv x) :=
      ⟨SSet.yonedaEquiv f, rfl, ht⟩
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e₀
    refine ⟨_, e, ?_, ?_⟩
    · have hmap : p.app (Opposite.op ⦋1⦌) e₀.edge = a₀.edge := by
        change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv f) = a₀.edge
        rw [← SSet.yonedaEquiv_comp, hfp, Equiv.apply_symm_apply]
      exact congrArg SSet.opObjEquiv.symm hmap
    · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_hasCocartesianHornLifting (SSet.opFunctor.map p) e).1
      exact hfc.op

/-- 概要：cartesian fibration の fiber の始対象は全空間の相対始点境界を充填する。
方針：反転した射の cocartesian 輸送を既存の fiber の判定へ渡す。
規約：始域と底は quasicategory。
使われ方：fiber の普遍余錐性から大域的な相対充填を得るための構造。 -/
@[kerodon 02WV]
lemma initialBoundaryLifting_of_isInitialVertex_fiber {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p]
    (b : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x.val := by
  have := cartesianFibration_op_toCocartesianHornFibration p
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.initialBoundaryLifting_of_isInitialVertex_fiber_op p b x hx

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.4.7"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_isInitialVertex_fiber
attribute [cite HTT "2.4.4.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_isInitialVertex_fiber
attribute [cite HTT "5.1.2.1" (partial := stronger-hyp) "仮定：Cartesian ファイブレーションの切断が各繊維で始対象（Lean が強い：底と全空間を準圏とする）。結論：各繊維の始対象から相対始点境界充填を得て、内部 Hom の同じ境界充填を恒等底図式の繊維に制限すると、指定切断が切断準圏の始対象となる（一致する場合）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_isInitialVertex_fiber
