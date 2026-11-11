module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeRightCosliceSection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomEdgeNaturality

/-!
概要：終端部分で同じ図式へ戻る変形に沿って、元の全余錐族を底を保って延長する。
方針：元の族を終端部分と底へ引き戻し、相対 coslice の充填を使う。
規約：両方の指定族を厳密に保持する。使われ方：固定終点根辺円柱の全 Hom 族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {K L J E B T : SSet.{u}} (q : E ⟶ B) [InnerFibration q]
  (t : K ⟶ E) (W : L ⟶ E) (r : K ⟶ L) (j : J ⟶ K) [Mono j]
  (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j) (hbase : r ≫ (W ≫ q) = t ≫ q)
  (hterminal : (j ≫ r) ≫ W = j ≫ t) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder W)

omit [InnerFibration q] [Mono j] in
/-- 終端部分へ制限した元の族と、底に引き戻した元の族は厳密に整合する。 -/
lemma relativeRetractCosliceFamily_compatible :
    (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction W (j ≫ r) hterminal) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (j ≫ t) q =
      ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (W ≫ q) r hbase) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (t ≫ q) j := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective ((j ≫ t) ≫ q)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap j (𝟙 T)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap r (𝟙 T)),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id, Category.assoc]

/-- 同じ終端部分と同じ底の族を持つ、全パラメータの実際の延長族。 -/
def relativeRetractCosliceFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_relativeRightCosliceFamily t q j hj
    (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction W (j ≫ r) hterminal)
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (W ≫ q) r hbase)
    (relativeRetractCosliceFamily_compatible q t W r j hbase hterminal a)).choose

/-- 終端部分への制限は元の族の同じ引き戻しそのもの。 -/
lemma relativeRetractCosliceFamily_terminal :
    relativeRetractCosliceFamily q t W r j hj hbase hterminal a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict t j =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction W (j ≫ r) hterminal :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_relativeRightCosliceFamily t q j hj
    (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction W (j ≫ r) hterminal)
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (W ≫ q) r hbase)
    (relativeRetractCosliceFamily_compatible q t W r j hbase hterminal a)).choose_spec.1

/-- 底の族は元の同じ族を r で引き戻したもの。 -/
lemma relativeRetractCosliceFamily_base :
    relativeRetractCosliceFamily q t W r j hj hbase hterminal a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp t q =
      (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (W ≫ q) r hbase :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_relativeRightCosliceFamily t q j hj
    (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction W (j ≫ r) hterminal)
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (W ≫ q) r hbase)
    (relativeRetractCosliceFamily_compatible q t W r j hbase hterminal a)).choose_spec.2

/-- 可変な終点の全族も、元の E 内の族を厳密に保持する。 -/
lemma relativeRetractCosliceFamily_projection :
    relativeRetractCosliceFamily q t W r j hj hbase hterminal a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection t j, ← Category.assoc,
    relativeRetractCosliceFamily_terminal, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
