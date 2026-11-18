module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexFrontComponentComparison
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeTerminalInjOn
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeTerminalNoninjective

/-!
概要：元の実二重 cone 単体は、退化を含む全作用素への厳密な自然性を持つ。
方針：前面成分は同じ全前面の等式、終端成分は選択集合上の単射と退化の二分岐を使う。
規約：全対象・全 cochain を保つ。使われ方：大域二重 join と二次 prism。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeData_pullback_map {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).toSimplexData.pullback (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).toSimplexData := by
  have ho : ((_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).toSimplexData.pullback
      (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ)).obj =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj := by
    funext i
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_obj_reindex A X Y c θ i
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext ho
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise ho
  intro I a b k hI ha hb hk
  by_cases hbl : b = Fin.last (m + 2)
  · by_cases hi : Set.InjOn (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ) (I : Set (Fin (m + 3)))
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_pullback_hom_terminal_injOn
        A X Y c θ I a b k hI ha hb hk hbl hi
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_pullback_hom_terminal_not_inj
        A X Y c θ I a b k hI ha hb hk hbl hi
  · have hfront := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_pullback_front A X Y c θ)
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data] at hfront
    exact _root_.SerrePositivity.ComplexLimits.complexSimplexData_hom_heq_of_front_eq A _ _ hfront I a b k hI ha hb hk hbl

lemma normalizedTensorDoubleConeSimplex_pullback_map {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).pullback (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeData_pullback_map A X Y c θ

end SerrePositivity.ComplexLimits
