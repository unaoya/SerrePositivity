module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.HomotopyPostcomposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyEvaluationClass

/-!
概要：全後合成ホモトピーの各関手成分を、同じ元のホモトピーの制限へ照合する。
方針：関手辺の往復と全後合成の評価を、同じ一次単体で接続する。
規約：端点の輸送は Arrow の等式で保持する。使われ方：実 slice 評価の全族の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof
/-- 後合成ホモトピーの関手辺は、元の同じ関手辺の全後合成作用による像。 -/
lemma homotopyPostcomposition_edge {X Y : SSet.{u}} (K : SSet.{u})
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K H)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap K X Y).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge := by
  change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm _))) = _
  rw [curry_uncurry, Equiv.apply_symm_apply]
  rfl
/-- 全後合成ホモトピーの成分は、元の同じ実ホモトピーを指定関手で制限した類。 -/
lemma homotopyPostcomposition_component_arrow {K X Y : SSet.{u}}
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) (a : K ⟶ X) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K H).h
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K H).h₀ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K H).h₁).app
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H a))) := by
  let e₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K H)).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom K).obj Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)))
  let e₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H a)
  have h₁ := congrArg (fun s => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom K).obj Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)).app (Opposite.op ⦋1⦌) s) (homotopyPostcomposition_edge K H)
  have h₂ := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.functorPostcompositionMap_evaluate a) (Opposite.op ⦋1⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge
  have h₃ : ((pre a).app Y).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge = e₂.edge := by
    change ((pre a).app Y).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry H.h)) = SSet.yonedaEquiv
        (curry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H a).h)
    rw [← SSet.yonedaEquiv_comp, curry_pre_app]
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.homotopyPostcomposition K H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)).symm.trans
      (Truncated.HomotopyCategory.congr_arrowMk_homMk e₁ e₂ (h₁.trans (h₂.trans h₃)))
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof
