module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.PointSliceOppositeUncurry
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.MappingPrismOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.PointSliceHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeCommaComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOpposite

/-!
概要：点の slice の標準指定変換の反転は coslice の標準指定変換と一致する。
方針：普遍余錐の反転と、左右の円柱比較の反転を合成する。
規約：両変換は実際の円柱の射として比較する。
使われ方：左 Kan の局所添字の反転比較が標準の矢印を表すことの証明。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：slice の標準変換の時間を第一因子へ直すと右の点付き円柱による展開となる。
方針：点を補う射と二因子を交換する射の成分を計算する。
規約：パラメータ A は任意。
使われ方：標準変換の反転を左右円柱の比較に帰着する。 -/
lemma kanPointSliceHomotopy_prism {A X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)) :
    (β_ (Δ[1] : SSet.{u}) A).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointSliceHomotopy x f).h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f := rfl

/-- 概要：正規化した反転の coslice の指定変換は元の slice の指定変換の反転。
方針：普遍錐の反転公式と、右の円柱の反転の公式を後合成する。
規約：quasicategory 性を使わない。
使われ方：局所添字の比較が標準の指定変換を保つことの入力。 -/
lemma kanPointSliceOverOpIso_homotopy {A X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointCosliceHomotopy (SSet.opObjEquiv.symm x)
      (SSet.opFunctor.map f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso x).hom.left)).h =
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointSliceHomotopy x f)).h := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism A.op ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 A.op) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A Δ[0]).inv := by
    have h := congrArg (fun z ↦ z ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A Δ[0]).inv)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.rightMappingSpacePrism_reverse A)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointCosliceHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointSliceOverOpIso_uncurry, kanPointSliceHomotopy_prism,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_postcomp, hp]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
