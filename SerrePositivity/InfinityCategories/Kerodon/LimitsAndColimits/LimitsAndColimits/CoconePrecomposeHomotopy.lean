module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePrecomposeNatTrans
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyFixedPoint

/-!
概要：指定自然変換による余錐の前合成を実ホモトピーで表示する。
方針：WithTerminal 上の拡張関手のホモトピーを標準余錐に沿って制限する。
規約：元の図式の指定変換と余錐の頂点を保持する。
使われ方：B5 の指定単位の左 Kan 局所輸送。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F G : I ⥤ C}

/-- 概要：余錐の脚の前合成を元の join の余錐のホモトピーとして表す。
方針：終対象を付加した関手の自然変換を join に制限する。
規約：元の指定変換と頂点を全時間で保持する。
使われ方：B5 の指定単位に沿う左 Kan の局所輸送。 -/
def nerveCoconePrecomposeHomotopy (c : Cocone G) (η : F ⟶ G) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv ((Cocone.precompose η).obj c)).val
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).val where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePrecomposeNatTrans c η)).h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, SSet.Homotopy.h₀,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_withTerminal]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, SSet.Homotopy.h₁,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_withTerminal]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：余錐のホモトピーは元の図式上で指定自然変換に一致する。
方針：終対象を付加した関手の自然変換を join に制限する。
規約：元の指定変換と頂点を全時間で保持する。
使われ方：B5 の指定単位に沿う左 Kan の局所輸送。 -/
lemma nerveCoconePrecomposeHomotopy_diagram (c : Cocone G) (η : F ⟶ G) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (nerve I) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (nerveCoconePrecomposeHomotopy c η).h =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η).h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (nerve I) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (nerve I) (Δ[0] : SSet.{u}) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone I)).val) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone I)).property,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_whiskerLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePrecomposeNatTrans_restrict]

/-- 概要：余錐の脚の前合成ホモトピーは元の指定頂点で時間に定値。
方針：終対象を付加した関手の自然変換を join に制限する。
規約：元の指定変換と頂点を全時間で保持する。
使われ方：B5 の指定単位に沿う左 Kan の局所輸送。 -/
lemma nerveCoconePrecomposeHomotopy_fixedVertex (c : Cocone G) (η : F ⟶ G) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (nerve I) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (nerveCoconePrecomposeHomotopy c η).h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (nerve I) (Δ[0] : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv c).val := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (nerve I) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalJoinNerveMap I ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (nerve I) (Δ[0] : SSet.{u}) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone I)).val) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_point, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_point]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_fixedPoint (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePrecomposeNatTrans c η)
    (WithTerminal.star : WithTerminal I) c.pt rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
