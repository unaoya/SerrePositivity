module

public import SerrePositivity.InfinityCategories.F1.CoherentHomComparison
public import SerrePositivity.InfinityCategories.F1.CoherentEdgeEquiv
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentOppositeIso

/-!
概要：coherent Hom の標準比較の零単体から、元の通常の射を厳密に回収する。
方針：二頂点の標準 path で Hom の作用を評価し、零単体の Yoneda の往復を使う。
規約：局所 Kan 性を仮定しない。
使われ方：pointed fiber の恒等点と標準一点 Hom 係数の一致を検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 標準右 Hom 比較の零単体は、元の豊穣零単体の通常の射データを持つ。 -/
lemma coherentHomComparisonSimplex_zero_arrowData
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    coherentNerveArrowData (coherentHomComparisonSimplex s) =
      ⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm s⟩ := by
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    ((pathLastMaximumMap (0 : Fin 1) ≫ SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentOnePath))⟩ : Σ A B : C, A ⟶ B) = _
  have h : (pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentOnePath) = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    ((SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌)
      ((pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentOnePath)))⟩ : Σ A B : C, A ⟶ B) = _
  rw [h, SSet.yonedaEquiv_symm_app_id]

/-- 標準右 Hom 比較の零単体は、元の通常の射の coherent な辺そのもの。 -/
lemma coherentHomComparisonSimplex_zero_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    coherentHomComparisonSimplex s =
      (coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).edge := by
  apply (coherentNerveArrowDataEquiv C).injective
  change coherentNerveArrowData (coherentHomComparisonSimplex s) =
    coherentNerveArrowData (coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).edge
  rw [coherentHomComparisonSimplex_zero_arrowData, coherentNerveEdge_edge,
    coherentNerveArrowData_of_arrow]

/-- 反対圏の右 Hom の零単体を反転しても、元の通常の射の同じ辺を回収する。 -/
lemma coherentLeftHomComparisonSimplex_zero_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    HomotopyLimits.coherentOppositeInverseSimplex
      (coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X) s) =
      (coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).edge := by
  apply (coherentNerveArrowDataEquiv C).injective
  change coherentNerveArrowData (HomotopyLimits.coherentOppositeInverseSimplex
    (coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X) s)) =
    coherentNerveArrowData (coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).edge
  rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow]
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    ((SSet.yonedaEquiv.symm s).app (Opposite.op ⦋0⦌)
      ((pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
        (((HomotopyLimits.coherentReverseThickening 1).map
          ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ coherentOnePath))))⟩ : Σ A B : C, A ⟶ B) = _
  have h : (pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
      (((HomotopyLimits.coherentReverseThickening 1).map
        ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentOnePath)) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  rw [h, SSet.yonedaEquiv_symm_app_id]

end SerrePositivity.InfinityCategories
