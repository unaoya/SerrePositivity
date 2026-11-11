module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsofibrationCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
/-!
概要：left fibration は、元の可逆辺を終点指定で持ち上げる categorical な持ち上げ性を持つ。
方針：指定終点への可逆辺の持ち上げと、その可逆性反映を既存の判定に適用する。
規約：元の指定辺・終点を厳密に保持し、モデル圏の仮定を要求しない。
使われ方：指定下側変換を元の全関手同型に沿って輸送する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
/-- 概要：left fibration は元の可逆辺を、指定終点と像を保って可逆に持ち上げる。
方針：辺の持ち上げと可逆性反映を使う。規約：指定値を保持。使われ方：相対輸送。 -/
lemma leftFibration_invertibleTargetLifting {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting p := by
  intro x d hd ht
  have ht' : Y.δ 0 (SSet.yonedaEquiv d) = p.app (Opposite.op ⦋0⦌) x := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ht, Equiv.apply_symm_apply]
  let ed : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (Y.δ 1 (SSet.yonedaEquiv d)) (p.app (Opposite.op ⦋0⦌) x) :=
    ⟨SSet.yonedaEquiv d, rfl, ht'⟩
  have hed : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ed :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ed) (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv d)) rfl).mpr hd
  obtain ⟨F, hFt, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftInvertibleEdge_target p x ed hed
  have hFd : F ≫ p = d := hFp.trans (Equiv.symm_apply_apply SSet.yonedaEquiv d)
  refine ⟨F, hFt, hFd, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge p
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv d)) ?_).mpr hd
  change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = SSet.yonedaEquiv d
  rw [← SSet.yonedaEquiv_comp, hFd]
/-- 概要：left fibration は単射な前合成同値に対する持ち上げ性を持つ。
方針：inner fibration と終点指定の可逆辺の判定を使う。
規約：追加の充填仮定は不要。使われ方：関手正方形の厳密化。 -/
lemma leftFibration_equivalenceLifting {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_of_innerFibration_of_targetLifting p
    (leftFibration_invertibleTargetLifting p)
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
