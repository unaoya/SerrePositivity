module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentOppositeIso

/-!
概要：coherent Hom の標準比較の零単体から、元の通常の射を厳密に回収する。
方針：二頂点の標準 path で Hom の作用を評価し、零単体の Yoneda の往復を使う。
規約：局所 Kan 性を仮定しない。
使われ方：pointed fiber の恒等点と標準一点 Hom 係数の一致を検証する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 標準右 Hom 比較の零単体は、元の豊穣零単体の通常の射データを持つ。 -/
lemma coherentHomComparisonSimplex_zero_arrowData
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex s) =
      ⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm s⟩ := by
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 1) ≫ SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath))⟩ : Σ A B : C, A ⟶ B) = _
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath) = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    ((SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath)))⟩ : Σ A B : C, A ⟶ B) = _
  rw [h, SSet.yonedaEquiv_symm_app_id]

/-- 標準右 Hom 比較の零単体は、元の通常の射の coherent な辺そのもの。 -/
lemma coherentHomComparisonSimplex_zero_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex s =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).edge := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv C).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex s) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).edge
  rw [coherentHomComparisonSimplex_zero_arrowData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow]

/-- 反対圏の右 Hom の零単体を反転しても、元の通常の射の同じ辺を回収する。 -/
lemma coherentLeftHomComparisonSimplex_zero_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeInverseSimplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X) s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).edge := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv C).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeInverseSimplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X) s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).edge
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow]
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    ((SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening 1).map
          ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath))))⟩ : Σ A B : C, A ⟶ B) = _
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening 1).map
        ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath)) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  rw [h, SSet.yonedaEquiv_symm_app_id]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
