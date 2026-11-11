module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightCanonicalCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConePostcomposeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
概要：指定余単位に沿う通常の右 Kan 局所錐を native な輸送として表示する。
方針：標準錐からの脚の後合成ホモトピーを comma の添字同型で移す。
規約：元の図式・指定余単位・錐の頂点を固定する。
使われ方：B5 の通常の pointwise 右 Kan の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]
  (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (α : L ⋙ F ⟶ F₀) (c : C)

/-- 概要：右 Kan の標準錐の比較を添字の逆同型へ移す。
方針：通常の錐の後合成を添字同型で移し、両端・図式・頂点を照合する。
規約：元の指定余単位を全時間で保持する。
使われ方：B5 の pointwise 右 Kan 条件の双方向比較。 -/
lemma nerveRightKanCanonicalCone_inv :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.classicalRightKanCanonicalCone L F c)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (nerveMap L) (nerveMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).val := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanCanonicalCone, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

/-- 概要：指定余単位の通常の局所錐から native な右 Kan の輸送を構成する。
方針：通常の錐の後合成を添字同型で移し、両端・図式・頂点を照合する。
規約：元の指定余単位を全時間で保持する。
使われ方：B5 の pointwise 右 Kan 条件の双方向比較。 -/
def nerveRightConeTransport : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport (nerveMap L) (nerveMap F₀) (nerveMap F)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy α) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) where
  family := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).inv ▷ Δ[1]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConePostcomposeHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.classicalRightKanCanonicalCone L F c)
      (Functor.whiskerLeft (StructuredArrow.proj c L) α)).h
  start := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, SSet.Homotopy.h₀]
    exact nerveRightKanCanonicalCone_inv L c
  diagram := by
    rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, comp_whiskerRight,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConePostcomposeHomotopy_diagram,
      ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_whiskerLeft, ← Category.assoc, ← comp_whiskerRight]
    have hp : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).inv ≫
        nerveMap (StructuredArrow.proj c L) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) := by
      rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso_hom_projection, Iso.inv_hom_id_assoc]
    rw [hp]
  fixedVertex := by
    rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConePostcomposeHomotopy_fixedVertex]
    have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape (nerveMap L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).inv =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (nerve (StructuredArrow c L)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
    rw [← hj, Category.assoc, nerveRightKanCanonicalCone_inv]

/-- 概要：輸送後の錐は通常の指定余単位の局所錐の nerve と一致する。
方針：通常の錐の後合成を添字同型で移し、両端・図式・頂点を照合する。
規約：元の指定余単位を全時間で保持する。
使われ方：B5 の pointwise 右 Kan 条件の双方向比較。 -/
lemma nerveRightConeTransport_cone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).hom ≫
      (nerveRightConeTransport L α c).cone.val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone ((Functor.RightExtension.mk F α).coneAt c)).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).hom ≫
    (SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).inv ▷ Δ[1]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConePostcomposeHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.classicalRightKanCanonicalCone L F c)
        (Functor.whiskerLeft (StructuredArrow.proj c L) α)).h) = _
  rw [← Category.assoc (SSet.ι₁), SSet.ι₁_comp, Category.assoc, SSet.Homotopy.h₁,
    ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Iso.hom_inv_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
