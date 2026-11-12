module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：余錐全体の二胞体の自然性から、脚の始点での成分の可逆性を判定する。
方針：join の標準交差辺に沿う自然性で、二本の脚と頂点成分の同型を消去する。
規約：二つの余錐の元の図式は異なってよい。
使われ方：局所 Kan 余錐の輸送から指定単位の成分へ可逆性を戻す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐の底の脚と頂点成分が可逆なら、その脚の始点での二胞体の成分も可逆。
方針：恒等余錐の交差辺を二つの余錐で写し、h 圏上の自然性の正方形を使う。
規約：指定された二胞体 α と脚 i を変更しない。
使われ方：左 Kan の局所輸送で単位の成分を評価する。 -/
lemma coconeHom_source_component_isIso {J D : SSet.{u}} [Quasicategory D]
    {p q : J ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom c.val d.val) (i : (Δ[0] : SSet.{u}) ⟶ J)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (c.leg i)) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (d.leg i))
    (ha : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr J (Δ[0] : SSet.{u}))))) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α (SSet.yonedaEquiv (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u})))) := by
  let b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u})) := ⟨𝟙 _, by rw [Category.comp_id]⟩
  let e := b.leg i
  have hce : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map c.val)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := c.leg i) ?_).2 hc
    change c.val.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (_ ≫ _ ≫ 𝟙 _)) =
      SSet.yonedaEquiv (_ ≫ _ ≫ c.val)
    rw [Category.comp_id, ← SSet.yonedaEquiv_comp, Category.assoc]
  have hde : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map d.val)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := d.leg i) ?_).2 hd
    change d.val.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (_ ≫ _ ≫ 𝟙 _)) =
      SSet.yonedaEquiv (_ ≫ _ ≫ d.val)
    rw [Category.comp_id, ← SSet.yonedaEquiv_comp, Category.assoc]
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorCellToNatTrans α
  have hn := τ.naturality (SSet.Truncated.HomotopyCategory.homMk e)
  dsimp only [τ] at hn
  erw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorCellToNatTrans_app_eq_evaluate, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorCellToNatTrans_app_eq_evaluate] at hn
  have : IsIso ((hoFunctor.map c.val).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk e)) := hce
  have : IsIso ((hoFunctor.map d.val).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk e)) := hde
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α b.vertex) := ha
  have hi : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α (SSet.yonedaEquiv (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0])) ≫
      (hoFunctor.map d.val).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk e)) := by
    erw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α (SSet.yonedaEquiv (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0])))
    ((hoFunctor.map d.val).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk e))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
