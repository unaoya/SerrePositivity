module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.ArrowSquareHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyInvertibility
/-!
概要：可逆な指定二成分を持つ実辺の可換正方形を、全関手圏の実同型にする。
方針：同じ四辺を実正方形に戻し、指定端点の可逆性で全区間関手の辺を可逆と判定する。
規約：Ho の Arrow の同型だけで止めない。使われ方：Verdier 分数表示から実辺の同型表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
/-- 可逆な指定二成分で可換な実辺は、区間上の全関手として同型。 -/
lemma nonempty_arrowFunctorIso_of_comm {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : Truncated.Edge (X := (truncation 2).obj X) x' y')
    (a : Truncated.Edge (X := (truncation 2).obj X) x x')
    (b : Truncated.Edge (X := (truncation 2).obj X) y y')
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge b)
    (h : Truncated.HomotopyCategory.homMk f ≫ Truncated.HomotopyCategory.homMk b =
      Truncated.HomotopyCategory.homMk a ≫ Truncated.HomotopyCategory.homMk g) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)) := by
  obtain ⟨H, h₀, h₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.exists_arrowHomotopy_of_homMk_comm f g a b h
  have : IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.arrowHomotopy_isInvertible_of_endpointPaths H a b ha hb h₀ h₁
  exact ⟨asIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
