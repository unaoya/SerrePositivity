module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofSliceFibration
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
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  {S : SSet.{u}} (f : S ⟶ roofTarget A Y q)

def roofQuillenDegreeCornerMap :
    pullback (f ≫ roofTargetProjection A Y q)
      (nerveMap (Over.forget (roofTargetDegree A Y q b))) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q) :=
  inv (roofQuillenDegreeNormalizationMap A Y q b f) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCornerBase (roofTargetProjection A Y q) f (SSet.yonedaEquiv.symm b)

lemma roofQuillenDegreeCorner_isPullback : IsPullback (pullback.snd f
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))) (roofQuillenSliceDegreeMap A Y q b f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCornerMap (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q))
      (roofQuillenDegreeCornerMap A Y q b f) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCorner_isPullback (roofTargetProjection A Y q) f
    (SSet.yonedaEquiv.symm b)).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (roofQuillenDegreeNormalizationMap A Y q b f)) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact (Category.comp_id _).trans (roofQuillenSliceDegreeMap_eq_native A Y q b f).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom, roofQuillenDegreeCornerMap,
      ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

lemma roofQuillenSlice_weaklyContractible_of_corner_weak [SSet.Quasicategory E]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q)]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (roofQuillenDegreeCornerMap A Y q b f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (roofQuillenSlice A Y q b f) := by
  have hi := Hammock.anodyneQ_map_isIso_of_weak _ h
  have hp := pointSliceCornerMap_fibration (SSet.yonedaEquiv.symm b)
    (roofTargetProjection A Y q)
  have hj := KST.Comparison.pullback_localized_isIso _ hi _
    ((SSet.modelCategoryQuillen.fibration_iff _).1 hp) _ _
    (roofQuillenDegreeCorner_isPullback A Y q b f)
  have hw := AnodyneWeakDetection.isWeakHomotopyEquivalence _ hj
  exact hw.weaklyContractible_iff.mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex b).isWeaklyContractible

end SerrePositivity.EInfinity.FrameHom.FrameArrows
