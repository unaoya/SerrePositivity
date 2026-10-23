module

public import SerrePositivity.InfinityCategories.F2.Ind.RepresentableTerminalValues
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredClosure
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFilteredTerminal

/-!
概要：Indκ に属する前層は、元の小さい圏の始対象を空間の終対象へ送る。
方針：表現可能値で証明し、同型と元の κ-filtered native 余極限の閉性を使う。
規約：ℵ₀ ≤ κ を明示。一般の有限極限交換は不要。
使われ方：元の Yoneda 因子化が零対象を保つことの始対象側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の Indκ 前層の始対象での評価値は、一般 coherent filtered 余極限の空形状交換で終対象。 -/
lemma indVertex_evaluation_isTerminal_of_initial (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) {C : SSet.{u}} [Quasicategory C]
    {z : C _⦋0⦌} (hz : IsInitialVertex z) {v : (PresheafInfinity C) _⦋0⦌}
    (hv : IsIndVertex κ C v) :
    IsTerminalVertex ((presheafInfinityEvaluation z).app (Opposite.op ⦋0⦌) v) := by
  apply hv (fun w => IsTerminalVertex
    ((presheafInfinityEvaluation z).app (Opposite.op ⦋0⦌) w))
  · intro y
    rw [yonedaInfinityMap_vertex]
    have he := evaluateFunctorAt_functorVertex (ULift.up (SSet.opObjEquiv.symm z))
      (representablePresheafInfinity y)
    exact (congrArg (fun s => IsTerminalVertex s) he).mpr
      (representablePresheafValue_isTerminal_of_initial hz y)
  · intro a b e ha
    exact ha.of_vertexIso (e.map (presheafInfinityEvaluation z))
  · intro I hI hFiltered D c hc hD
    let : IsFilteredInfinity I := isFilteredInfinity_of_isKappaFiltered hκ I
    have he := presheafInfinity_evaluation_isColimit D c hc z
    have ht := coherentFilteredColimitVertex_isTerminal
      (D ≫ presheafInfinityEvaluation z) hD
      (mapJoinCocone (presheafInfinityEvaluation z) c) he
    rw [mapJoinCocone_vertex] at ht
    exact ht

end SerrePositivity.InfinityCategories.F2.Ind
