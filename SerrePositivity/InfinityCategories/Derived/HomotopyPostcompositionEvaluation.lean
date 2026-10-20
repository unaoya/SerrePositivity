module
public import SerrePositivity.InfinityCategories.Derived.HomotopyPostcomposition
public import SerrePositivity.InfinityCategories.Stable.HomotopyEvaluationClass

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
namespace SerrePositivity.InfinityCategories
/-- 後合成ホモトピーの関手辺は、元の同じ関手辺の全後合成作用による像。 -/
lemma homotopyPostcomposition_edge {X Y : SSet.{u}} (K : SSet.{u})
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    (functorEdgeOfSimplicialHomotopy (homotopyPostcomposition K H)).edge =
      (functorPostcompositionMap K X Y).app (Opposite.op ⦋1⦌)
        (functorEdgeOfSimplicialHomotopy H).edge := by
  change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm _))) = _
  rw [curry_uncurry, Equiv.apply_symm_apply]
  rfl
/-- 全後合成ホモトピーの成分は、元の同じ実ホモトピーを指定関手で制限した類。 -/
lemma homotopyPostcomposition_component_arrow {K X Y : SSet.{u}}
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) (a : K ⟶ X) :
    Arrow.mk ((homotopyNatTransOfEndpoints (homotopyPostcomposition K H).h
      (homotopyPostcomposition K H).h₀ (homotopyPostcomposition K H).h₁).app
        (SSet.HomotopyCategory.mk (functorVertex a))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H a))) := by
  let e₁ := (functorEdgeOfSimplicialHomotopy (homotopyPostcomposition K H)).map
    ((truncation 2).map (evaluateFunctorAt (Y := (ihom K).obj Y) (functorVertex a)))
  let e₂ := functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H a)
  have h₁ := congrArg (fun s => (evaluateFunctorAt (Y := (ihom K).obj Y)
    (functorVertex a)).app (Opposite.op ⦋1⦌) s) (homotopyPostcomposition_edge K H)
  have h₂ := ConcreteCategory.congr_hom
    (NatTrans.congr_app (functorPostcompositionMap_evaluate a) (Opposite.op ⦋1⦌))
      (functorEdgeOfSimplicialHomotopy H).edge
  have h₃ : ((pre a).app Y).app (Opposite.op ⦋1⦌)
      (functorEdgeOfSimplicialHomotopy H).edge = e₂.edge := by
    change ((pre a).app Y).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (curry H.h)) = SSet.yonedaEquiv
        (curry (functorHomotopyPrecomp H a).h)
    rw [← SSet.yonedaEquiv_comp, curry_pre_app]
    rfl
  exact (homotopyEvaluationOfEndpoints_arrow (homotopyPostcomposition K H)
    (functorVertex a)).symm.trans
      (Truncated.HomotopyCategory.congr_arrowMk_homMk e₁ e₂ (h₁.trans (h₂.trans h₃)))
end SerrePositivity.InfinityCategories
