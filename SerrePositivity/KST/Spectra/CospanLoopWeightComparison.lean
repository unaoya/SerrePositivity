module

public import SerrePositivity.KST.Spectra.CospanLoopWeights
public import SerrePositivity.KST.Spectra.CospanCentralWeightRestriction
public import SerrePositivity.KST.Spectra.SplitTrivialSpanHomotopy

/-!
概要：ホーンを区間へ潰す loop 重みの射が誘導する、実際の end のホモトピー同値。
方針：共通の二単体重みからの二つの制限の自明 Kan 性と、厳密な区間への射影を使う。
規約：係数の中央の Kan 性だけ。使われ方：固定 cospan の Hom–end を基点付き loop へ移す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra
open SerrePositivity.InfinityCategories
variable (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
  [KanComplex (H.obj (AsSmall.up.obj .one))]

/-- 二単体重みから区間重みへの制限は、実際の trivial Kan fibration。 -/
lemma loopIntervalWeightRestriction_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopIntervalToTriangle H) := by
  have leftIso : IsIso (loopIntervalToTriangle.{u}.app (AsSmall.up.obj .left)) := by
    change IsIso (𝟙 (stdSimplex.obj ⦋0⦌))
    infer_instance
  have rightIso : IsIso (loopIntervalToTriangle.{u}.app (AsSmall.up.obj .right)) := by
    change IsIso (𝟙 (stdSimplex.obj ⦋0⦌))
    infer_instance
  exact weightedSectionsPre_central_trivialKanFibration _
    loopIntervalToTriangle_central_anodyne

/-- 二単体重みからホーン重みへの制限も、実際の trivial Kan fibration。 -/
lemma loopHornWeightRestriction_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopHornToTriangle H) := by
  have leftIso : IsIso (loopHornToTriangle.{u}.app (AsSmall.up.obj .left)) := by
    change IsIso (𝟙 (stdSimplex.obj ⦋0⦌))
    infer_instance
  have rightIso : IsIso (loopHornToTriangle.{u}.app (AsSmall.up.obj .right)) := by
    change IsIso (𝟙 (stdSimplex.obj ⦋0⦌))
    infer_instance
  exact weightedSectionsPre_central_trivialKanFibration _ loopHornToTriangle_central_anodyne

omit [KanComplex (H.obj (AsSmall.up.obj .one))] in
/-- 区間への射影による end の射は、区間への制限の厳密な切断。 -/
lemma loopIntervalWeightRestriction_section :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopTriangleToInterval H ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopIntervalToTriangle H =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight H) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp, loopIntervalToTriangle_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_id]

omit [KanComplex (H.obj (AsSmall.up.obj .one))] in
/-- ホーンの一辺を潰す比較射は、指定した二単体を介する制限の合成そのもの。 -/
lemma loopHornCollapseEnd_factor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopHornCollapse H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopTriangleToInterval H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopHornToTriangle H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp _ _ _

/-- loop のホーン重みと区間重みは、指定した collapse による元の end の射でホモトピー同値。 -/
lemma loopHornCollapseEnd_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopHornCollapse H) := by
  have intervalTrivial := loopIntervalWeightRestriction_trivialKanFibration H
  have hornTrivial := loopHornWeightRestriction_trivialKanFibration H
  rw [loopHornCollapseEnd_factor]
  exact homotopyEquivalence_of_split_trivial_span
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopIntervalToTriangle H) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopHornToTriangle H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre loopTriangleToInterval H) (loopIntervalWeightRestriction_section H)

end SerrePositivity.KST.Spectra
