module


public meta import SerrePositivity.Util.Citation
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

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.1.1" (partial := special) "仮定：各部分図式に余極限が存在する（Lean が強い：標的と各添字は通常の圏の神経。離散圏上の Grothendieck 構成を添字の非交和に取る）。結論：全図式の余極限余錐と部分余極限を頂点とする離散図式の余極限余錐を相互に移す（一致する場合。任意の準圏・単体集合形状は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_isColimit_iff
attribute [cite HTT "4.4.3.2" (partial := special) "仮定：余等化子と小余積が存在する（Lean が強い：通常の圏の神経を標的に、添字も固定宇宙の通常の圏の神経に限る）。結論：通常の圏で全小余極限を得て、同じ図式の神経の余極限存在へ移せる（一致する向きと範囲。任意の単体集合形状、濃度 κ による切断と逆向きは含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerve_hasColimit_iff
attribute [cite HTT "5.1.5.7" (partial := special) "仮定：準圏の充満部分圏（Lean が強い：通常の圏の神経と通常圏の神経を形状とする図式）。結論：同じ部分圏内の図式の任意の余極限余錐の頂点が再びその部分圏に属するという閉性を定める（一致する場合。任意の単体集合形状は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_isColimit_iff
