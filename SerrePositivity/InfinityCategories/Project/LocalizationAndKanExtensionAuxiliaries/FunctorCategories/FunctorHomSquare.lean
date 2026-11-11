module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.DegenerateFunctorHomSquare

/-!
概要：四辺を指定した関手正方形と、可逆な左辺による上辺の比較。
方針：二つの三角形の合成関係を使い、h Fun の左辺を消去する。
規約：正方形も各辺も実際の単体集合の射として保持する。
使われ方：相対 join の厳密化前後の指定自然変換のクラスの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：四つの指定ホモトピーを境界に持つ関手正方形。
方針：各辺の curry が正方形の制限に等しいことを記録する。
規約：下辺・上辺・左辺・右辺の順。
使われ方：任意の正方形の h Fun の合成関係。 -/
structure FunctorHomSquare {A X : SSet.{u}} {U₀ U₁ V₀ V₁ : A ⟶ X}
    (b : SSet.Homotopy U₀ U₁) (t : SSet.Homotopy V₀ V₁)
    (l : SSet.Homotopy U₀ V₀) (r : SSet.Homotopy U₁ V₁) where
  diagram : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X
  bottom : SSet.ι₀ ≫ diagram = curry b.h
  top : SSet.ι₁ ≫ diagram = curry t.h
  left : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ diagram = curry l.h
  right : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ diagram = curry r.h

/-- 概要：指定四辺の正方形は h Fun の可換性を与える。
方針：一般の正方形の合成関係に各辺の厳密な表示を入れる。
規約：標的の quasicategory 性は不要。
使われ方：補正ホモトピーと円柱比較の合成関係。 -/
lemma FunctorHomSquare.hom_relation {A X : SSet.{u}} {U₀ U₁ V₀ V₁ : A ⟶ X}
    {b : SSet.Homotopy U₀ U₁} {t : SSet.Homotopy V₀ V₁}
    {l : SSet.Homotopy U₀ V₀} {r : SSet.Homotopy U₁ V₁}
    (s : FunctorHomSquare b t l r) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homMk_comp_eq_of_square
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) s.diagram
  · change s.diagram.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    exact congrArg SSet.yonedaEquiv s.bottom
  · change s.diagram.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    exact congrArg SSet.yonedaEquiv s.top
  · change s.diagram.app (Opposite.op ⦋1⦌) (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← hi]
    exact congrArg SSet.yonedaEquiv s.left
  · change s.diagram.app (Opposite.op ⦋1⦌) (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← hi]
    exact congrArg SSet.yonedaEquiv s.right

/-- 概要：下辺と両側辺が同じ二つの正方形では、可逆な左辺を消去して上辺の類が一致する。
方針：二つの可換性を比較し、h Fun の同型である左辺を消去する。
規約：各点の等式からではなく h Fun 全体の合成関係から導く。
使われ方：指定自然変換の類の厳密化による保存。 -/
lemma functorHomSquare_top_hom_eq {A X : SSet.{u}} {U₀ U₁ V₀ V₁ : A ⟶ X}
    {b : SSet.Homotopy U₀ U₁} {t₀ t₁ : SSet.Homotopy V₀ V₁}
    {l : SSet.Homotopy U₀ V₀} {r : SSet.Homotopy U₁ V₁}
    (s₀ : FunctorHomSquare b t₀ l r) (s₁ : FunctorHomSquare b t₁ l r)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l)) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t₀) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t₁) := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l)) := hl
  apply (cancel_epi
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l))).1
  exact s₀.hom_relation.symm.trans s₁.hom_relation

/-- 概要：両側辺の代表が異なっても、その類が等しければ二つの上辺の類は一致する。
方針：二つの正方形の合成関係で両側辺の類を置き換え、左の同型を消去する。
規約：raw な辺の等式を仮定せず、h Fun の等式を使う。
使われ方：同型の選んだ代表を変更する端点の厳密化。 -/
lemma functorHomSquare_top_hom_eq_of_boundary_classes
    {A X : SSet.{u}} {U₀ U₁ V₀ V₁ : A ⟶ X}
    {b : SSet.Homotopy U₀ U₁} {t₀ t₁ : SSet.Homotopy V₀ V₁}
    {l₀ l₁ : SSet.Homotopy U₀ V₀} {r₀ r₁ : SSet.Homotopy U₁ V₁}
    (s₀ : FunctorHomSquare b t₀ l₀ r₀) (s₁ : FunctorHomSquare b t₁ l₁ r₁)
    (hl : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l₀) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l₁))
    (hr : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r₀) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r₁))
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l₀)) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t₀) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t₁) := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l₀)) := hi
  apply (cancel_epi
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l₀))).1
  calc
    _ = _ := s₀.hom_relation.symm
    _ = _ := congrArg
      (fun t ↦ SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b) ≫ t) hr
    _ = _ := s₁.hom_relation
    _ = _ := congrArg
      (fun t ↦ t ≫ SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy t₁)) hl.symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
