module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RelativeSliceRightFibration
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InitialIndexSlice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws
/-!
概要：inner fibration の実 slice を、標的の slice と元の始域の corner へ写すと右ファイブレーション。
方針：空部分図式の相対 slice の右ファイブレーションを、空 slice の厳密同型で正規化する。
規約：モデル圏構造は使わない。使われ方：商側三角形から商屋根への右ファイブレーション。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
variable {K E B : SSet.{u}} (p : K ⟶ E) (r : E ⟶ B)
/-- 標的の実 slice と元の同じ始域を保持する corner。 -/
def sliceOverCorner : SSet.{u} := pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ r)) r
/-- 実 slice の各錐を、標的の全錐と元の始域の組へ写す。 -/
def sliceOverCornerMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p ⟶ sliceOverCorner p r :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection p r)
/-- 空部分図式の相対 slice を、元の始域を記憶する corner へ厳密に正規化する。 -/
def relativeSliceEmptyCornerMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOver p (⊥ : K.Subcomplex).ι r ⟶ sliceOverCorner p r :=
  pullback.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (p ≫ r) (⊥ : K.Subcomplex).ι)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp ((⊥ : K.Subcomplex).ι ≫ p) r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ r)) r (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((⊥ : K.Subcomplex).ι ≫ p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (((⊥ : K.Subcomplex).ι ≫ p) ≫ r))
    (by simpa only [Category.id_comp] using!
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverRestrict_projection (p ≫ r) (⊥ : K.Subcomplex).ι)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection ((⊥ : K.Subcomplex).ι ≫ p) r)
/-- 空部分図式の正規化は、全次数で厳密な同型。 -/
instance relativeSliceEmptyCornerMap_isIso : IsIso (relativeSliceEmptyCornerMap p r) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.initialIndexSliceProjection_isIso Subcomplex.isInitialBot
    ((⊥ : K.Subcomplex).ι ≫ p)
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.initialIndexSliceProjection_isIso Subcomplex.isInitialBot
    (((⊥ : K.Subcomplex).ι ≫ p) ≫ r)
  dsimp only [relativeSliceEmptyCornerMap]
  infer_instance
/-- 空相対 slice の正規化は、元の同じ全錐の corner 写像を回収する。 -/
lemma relativeSliceOverMap_empty_corner :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap p (⊥ : K.Subcomplex).ι r ≫ relativeSliceEmptyCornerMap p r =
      sliceOverCornerMap p r := by
  apply pullback.hom_ext
  · dsimp only [relativeSliceEmptyCornerMap, sliceOverCornerMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap,
      pullback.map]
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
      pullback.lift_fst, Category.comp_id, pullback.lift_fst]
  · dsimp only [relativeSliceEmptyCornerMap, sliceOverCornerMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap,
      pullback.map]
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
      pullback.lift_snd, pullback.lift_snd]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverRestrict_projection p (⊥ : K.Subcomplex).ι
/-- inner fibration の実 slice の corner 比較は右ファイブレーション。 -/
instance sliceOverCornerMap_rightFibration [InnerFibration r] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (sliceOverCornerMap p r) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (relativeSliceEmptyCornerMap p r) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.of_isIso _⟩
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap p (⊥ : K.Subcomplex).ι r ≫
      relativeSliceEmptyCornerMap p r) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.comp_mem _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem⟩
  rw [relativeSliceOverMap_empty_corner] at h
  exact h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
