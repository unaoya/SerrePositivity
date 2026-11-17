module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSliceFibration
public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization
public import SerrePositivity.KST.Comparison.ArbitraryBasePullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceIdentityTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility

/-!
# 元の次数比較による実屋根 slice の弱可縮性の還元

概要：実 slice を相対始点評価の厳密な引き戻しとして保持する。
方針：既証の任意底の Kan 引き戻し不変性で、次数側の弱比較を全錐へ戻す。
規約：元の指定点・全高次錐を保つ。次数側の弱同値性自体は別途証明が必要。
使われ方：元の sourceFrameHom×Δ[n] の全単体比較から Quillen A の条件へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories
open _root_.SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget A Y q) _⦋0⦌)
  {S : SSet.{u}} (f : S ⟶ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget A Y q)

def roofQuillenDegreeCornerMap :
    pullback (f ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q)
      (nerveMap (Over.forget (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b))) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) :=
  inv (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap A Y q b f) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCornerBase (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) f (SSet.yonedaEquiv.symm b)

lemma roofQuillenDegreeCorner_isPullback : IsPullback (pullback.snd f
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceDegreeMap A Y q b f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCornerMap (SSet.yonedaEquiv.symm b) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeCornerMap A Y q b f) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCorner_isPullback (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) f
    (SSet.yonedaEquiv.symm b)).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap A Y q b f)) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact (Category.comp_id _).trans (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceDegreeMap_eq_native A Y q b f).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeCornerMap,
      ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

lemma roofQuillenSlice_weaklyContractible_of_corner_weak [SSet.Quasicategory E]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q)]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeCornerMap A Y q b f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSlice A Y q b f) := by
  have hi := _root_.SerrePositivity.EInfinity.Hammock.anodyneQ_map_isIso_of_weak _ h
  have hp := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.pointSliceCornerMap_fibration (SSet.yonedaEquiv.symm b)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q)
  have hj := _root_.SerrePositivity.KST.Comparison.pullback_localized_isIso _ hi _
    ((SSet.modelCategoryQuillen.fibration_iff _).1 hp) _ _
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeCorner_isPullback A Y q b f)
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ hj
  exact hw.weaklyContractible_iff.mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex b).isWeaklyContractible

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
