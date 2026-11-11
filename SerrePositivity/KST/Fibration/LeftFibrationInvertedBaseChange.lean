module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-! # 全辺が可逆になる底図式上の、元の左 fibration の cartesian 性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 左 fibration を可逆な全辺の図式へ引き戻すと、元の実 lift によって cartesian にもなる。 -/
theorem leftFibrationBaseChange_cartesian_of_inverts {E Q D : SSet.{u}} [Quasicategory Q]
    (p : E ⟶ Q) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (k : D ⟶ Q) (hk : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges k Set.univ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.snd p k) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  refine ⟨innerFibrations.pullback_snd p k (InnerFibration.mem (q := p)), ?_⟩
  intro v e he
  change stdSimplex.δ (0 : Fin 2) ≫ e =
    yonedaEquiv.symm ((pullback.snd p k).app (Opposite.op ⦋0⦌) v) at he
  let w := (pullback.fst p k).app (Opposite.op ⦋0⦌) v
  have hb : stdSimplex.δ (0 : Fin 2) ≫ (e ≫ k) =
      yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) w) := by
    rw [← Category.assoc, he]
    have hc := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
      (pullback.condition (f := p) (g := k))
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, NatTrans.comp_app_apply, w]
      using hc.symm
  have ht : Q.δ 0 (yonedaEquiv (e ≫ k)) = p.app (Opposite.op ⦋0⦌) w := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hb, Equiv.apply_symm_apply]
  let s : Truncated.Edge (X := (truncation 2).obj Q)
      (Q.δ 1 (yonedaEquiv (e ≫ k))) (p.app (Opposite.op ⦋0⦌) w) :=
    ⟨yonedaEquiv (e ≫ k), rfl, ht⟩
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge s := by
    have hi := hk (a := yonedaEquiv e) (Set.mem_univ _)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (yonedaEquiv e)).map
      ((truncation 2).map k)) (f := s) (yonedaEquiv_comp e k).symm).mp
    exact hi
  obtain ⟨G, hG, hGp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftInvertibleEdge_target p w s hs
  have hGk : G ≫ p = e ≫ k := hGp.trans (yonedaEquiv.symm_apply_apply _)
  have hGi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (yonedaEquiv G)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge p
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := s) (show
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (yonedaEquiv G)).map ((truncation 2).map p)).edge = s.edge from
        (yonedaEquiv_comp G p).symm.trans (congrArg SSet.yonedaEquiv hGk))).mpr
    exact hs
  have hGc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isInvertibleEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (yonedaEquiv G)) hGi
  refine ⟨pullback.lift G e hGk, ?_, pullback.lift_snd _ _ _, ?_⟩
  · apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, yonedaEquiv_symm_comp] using hG
    · simpa only [Category.assoc, pullback.lift_snd, yonedaEquiv_symm_comp] using he
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback
    rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
    exact hGc

end SerrePositivity.KST.Fibration
