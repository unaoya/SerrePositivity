module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeEquiv
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BNerveComparisonLimit
public import Mathlib.CategoryTheory.Limits.Opposites

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

/-- 概要：通常の指定余錐の余極限性と native な余極限性は同値。
方針：反転と図式同型の射影公式を使う。
規約：指定した元の図式と余錐を保持する。
使われ方：B5 の局所余極限の双方向比較。 -/
lemma nerveCocone_isColimit_iff (c : Cocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c) ↔ Nonempty (IsColimit c) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveOppositeSliceIso (F := F)).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c.op) := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseConeEquiv (nerveMap F))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseConeEquiv (nerveMap F)).symm _) = _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseConeEquiv (nerveMap F)).apply_symm_apply _
  rw [he]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c.op) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveOppositeSliceIso (F := F)).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c.op)) :=
    ⟨fun h ↦ h.map_of_isIso _, fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration _ h⟩
  rw [← hi]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_isLimit_iff]
  exact ⟨fun ⟨h⟩ ↦ ⟨h.unop⟩, fun ⟨h⟩ ↦ ⟨h.op⟩⟩

/-- 概要：任意の native な余錐の余極限性を通常の余錐へ読み戻す。
方針：余錐の全単射の右逆性で指定余錐の判定に帰着する。
規約：元の図式と native な指定余錐を保持する。
使われ方：B5 の native な局所条件の回収。 -/
lemma nerveCoconeEquiv_symm_isColimit_iff (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ Nonempty (IsColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (F := F)).symm c)) := by
  have h := nerveCocone_isColimit_iff ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (F := F)).symm c)
  rwa [Equiv.apply_symm_apply] at h

/-- 概要：通常の図式の余極限の存在と nerve の余極限の存在は同値。
方針：余錐の全単射と指定余錐の普遍性の比較を使う。
規約：同じ宇宙の小さい圏上の任意の図式を扱う。
使われ方：B5 の左 Kan 拡張の点ごとの存在条件の回収。 -/
lemma nerve_hasColimit_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (nerveMap F) ↔ Limits.HasColimit F := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨h⟩ := (nerveCoconeEquiv_symm_isColimit_iff c).1 hc
    exact ⟨⟨⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (F := F)).symm c, h⟩⟩⟩
  · intro h
    let := h
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (colimit.cocone F),
      (nerveCocone_isColimit_iff _).2 ⟨colimit.isColimit F⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
