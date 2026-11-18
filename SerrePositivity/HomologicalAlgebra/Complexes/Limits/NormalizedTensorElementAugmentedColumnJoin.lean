module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementAugmentedColumn

/-!
概要：通常 augmentation の終端付き実列は、同じ混合宇宙の余錐 join の全単体制限である。
方針：元の持ち上げた有限列の余錐表示へ同じ down を合成し、全列を回収する。
規約：元の c・augmentation・上下写像を保持する。使われ方：大域実 slice 図式の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementAugmentedColumn_join {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := nerve (Complex A))).symm
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.coconeJoin (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationCocone A X Y) := by
  let Γ := c ⋙ ULiftHom.up.{u, u + 1, u + 1}
  let L := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftedAugmentationCocone A X Y
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_join L Γ
  have hd := congrArg (fun f => f ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (Complex A)) h
  simp only [Category.assoc, SSet.yonedaEquiv_symm_comp] at hd
  have hu : (SSet.yonedaEquiv (X := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y))).symm c ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.up (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) =
      (SSet.yonedaEquiv (X := nerve (ULiftHom.{u + 1}
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)))).symm Γ := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.up (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (𝟙 Δ[0]) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm Γ) (𝟙 Δ[0]) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, hu, Category.id_comp]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm c) (𝟙 Δ[0]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.up (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv L).val ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (Complex A))
  rw [← Category.assoc, hm]
  exact hd

end SerrePositivity.ComplexLimits
