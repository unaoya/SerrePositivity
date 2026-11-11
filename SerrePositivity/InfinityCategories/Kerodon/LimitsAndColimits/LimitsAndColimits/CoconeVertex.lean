module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeEquiv

/-!
概要：通常の余錐と nerve の余錐を反転によって比較する。
方針：反対圏の nerve の同型と slice の同型を合成する。
規約：図式・余錐・頂点を固定し、同じ宇宙の小さい圏を扱う。
使われ方：B5 の局所余極限と pointwise Kan の古典比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：余錐の反転は頂点の反転を与える。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
lemma coconeReverseCone_vertex {K X : SSet.{u}} {p : K ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone d).vertex = SSet.opObjEquiv.symm d.vertex := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso_projection p) (Opposite.op ⦋0⦌)) (SSet.opObjEquiv.symm d)
  exact h
/-- 概要：nerve へ移した余錐は通常の指定頂点を保つ。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
lemma nerveCocone_vertex (c : Cocone F) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c.pt := by
  apply SSet.opObjEquiv.symm.injective
  rw [← coconeReverseCone_vertex]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveOppositeSliceIso (F := F)).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c.op) := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseConeEquiv (nerveMap F))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseConeEquiv (nerveMap F)).symm _) = _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseConeEquiv (nerveMap F)).apply_symm_apply _
  rw [he]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceDiagramIso_projection (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeIso I) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeIso C) _ _
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeIso_natural I F)) (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c.op)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.opFunctor.map (nerveMap F))).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveOppositeSliceIso (F := F)).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c.op)) =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeIso C).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c.op).vertex at h
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.opFunctor.map (nerveMap F))).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveOppositeSliceIso (F := F)).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c.op)) = _
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_vertex]
  rfl

/-- 概要：読み戻した通常の余錐の頂点は元の native な頂点を表す。
方針：前向きの頂点公式と余錐の全単射の右逆性を使う。
規約：元の図式と native な指定余錐を保持する。
使われ方：B5 の指定局所余錐の復元。 -/
lemma nerveCoconeEquiv_symm_vertex (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (F := F)).symm c).pt = c.vertex := by
  have h := nerveCocone_vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (F := F)).symm c)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
