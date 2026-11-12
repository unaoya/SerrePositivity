module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.SliceWeakContractibility

/-!
概要：Quillen A の right cofinality から弱可縮な coslice への必要性。
方針：coslice 射影が left fibration であることと cofinality の引き戻し保存を使う。
規約：標的だけが quasicategory。元の始域や引き戻した coslice の Kan 性は不要。
使われ方：Kerodon Theorem 7.2.3.1(2)（Tag 02NY） の順方向。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：right cofinal な射の coslice への引き戻しの射影も right cofinal。
方針：coslice 射影の left fibration 性を使い、引き戻しの対称性で向きを揃える。
規約：標的 B だけに quasicategory 性を仮定する。
使われ方：Quillen A の必要性で弱同値となる元の射影を明示する。 -/
lemma IsRightCofinal.cosliceProjection_isRightCofinal {A B : SSet.{u}} [Quasicategory B]
    {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (pullback.snd f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b))) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_isRightCofinal p f hf
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne (pullbackSymmetry f p).hom
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions _)
  have hh := hi.comp h
  simpa only [pullbackSymmetry_hom_comp_fst] using hh

/-- 概要：right cofinal な射の各 coslice 引き戻しは弱可縮。
方針：coslice への射影の cofinality から弱同値性を得て、恒等余錐による弱可縮性を戻す。
規約：弱可縮性であり、引き戻しの Kan 性や ∞ 圏としての可縮性は要求しない。
使われ方：Kerodon Theorem 7.2.3.1(2)（Tag 02NY）、HTT Theorem 4.1.3.1 の必要性。 -/
lemma IsRightCofinal.coslice_isWeaklyContractible {A B : SSet.{u}} [Quasicategory B]
    {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b))) :=
  (hf.cosliceProjection_isRightCofinal b).isWeakHomotopyEquivalence.weaklyContractible_iff.mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnder_isWeaklyContractible b)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
