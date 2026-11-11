module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FixedHomotopyComponent

/-! # ホモトピーの関手辺と評価した成分の類

概要：ホモトピーの関手辺を頂点で評価した類は、h の自然変換の成分と一致する。
方針：uncurry した辺を元のホモトピーへ戻し、両者の一次単体を比較する。
規約：端点の輸送は Arrow の等式に含める。
使われ方：S4 の始点を固定した span 比較の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：ホモトピーの関手辺を評価した類は自然変換の頂点成分と一致する。
方針：二重の curry／uncurry を消し、辺の同じ一次単体を比較する。
規約：quasicategory 性は不要。使われ方：固定した始点成分の判定。 -/
lemma homotopyEvaluation_arrow {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) (a : A _⦋0⦌) :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))) =
        Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans H.h).app (SSet.HomotopyCategory.mk a)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H
  let e₁ := e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))
  let e₂ := ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).tensor
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map H.h)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge e a
  have hH : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h = H.h := by
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = H.h
    rw [Equiv.symm_apply_apply, uncurry_curry]
  have heq : e₁.edge = e₂.edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a).app (Opposite.op ⦋1⦌) e.edge =
      H.h.app (Opposite.op ⦋1⦌)
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a).app (Opposite.op ⦋1⦌) e.edge at he
    rw [hH] at he
    exact he.symm
  change Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e₁) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e₂)
  exact SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk e₁ e₂ heq

/-- 概要：両端を指定した自然変換の頂点成分もホモトピーの評価した類と一致する。
方針：両端の等式による輸送を Arrow の等号に含める。
規約：quasicategory 性は不要。使われ方：短複体の比較成分の照合。 -/
lemma homotopyEvaluationOfEndpoints_arrow {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) (a : A _⦋0⦌) :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))) =
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app (SSet.HomotopyCategory.mk a)) := by
  have ht (U : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) {f g : A ⟶ X}
      (h₀ : SSet.ι₀ ≫ U = f) (h₁ : SSet.ι₁ ≫ U = g) :
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints U h₀ h₁).app (SSet.HomotopyCategory.mk a)) =
        Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans U).app (SSet.HomotopyCategory.mk a)) := by
    subst f g
    rfl
  exact (homotopyEvaluation_arrow H a).trans (ht H.h H.h₀ H.h₁).symm

/-- 概要：同じ頂点で同じ値に固定された二つのホモトピーの評価した類は一致する。
方針：両方の評価した類を同じ恒等成分へ移し、固定した端点間の Arrow の等号を消す。
規約：quasicategory 性は不要。使われ方：始点固定の図式の比較の一意性。 -/
lemma homotopyEvaluation_eq_of_fixedVertex {A X : SSet.{u}} {F G : A ⟶ X}
    (H J : SSet.Homotopy F G) (i : (Δ[0] : SSet.{u}) ⟶ A) (x : X _⦋0⦌)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const x)
    (hJ : (i ▷ (Δ[1] : SSet.{u})) ≫ J.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const x) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.yonedaEquiv i))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.yonedaEquiv i))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J)) := by
  apply Arrow.mk_injective
  have h₀ := (homotopyEvaluation_arrow H (SSet.yonedaEquiv i)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow H.h i x hH)
  have h₁ := (homotopyEvaluation_arrow J (SSet.yonedaEquiv i)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow J.h i x hJ)
  exact h₀.trans h₁.symm

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
