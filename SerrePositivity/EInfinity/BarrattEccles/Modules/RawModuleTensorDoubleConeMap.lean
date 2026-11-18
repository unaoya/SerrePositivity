module
public import SerrePositivity.EInfinity.Modules.FrontComponentComparison
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeTerminalInjOn
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeTerminalNoninjective

/-!
概要：元の実二重 cone 単体は、退化を含む全作用素への厳密な自然性を持つ。
方針：前面成分は同じ全前面の等式、終端成分は選択集合上の単射と退化の二分岐を使う。
規約：HA Construction 1.3.1.6・1.3.1.13、全対象・全 cochain を保つ。使われ方：大域二重 join と二次 prism。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeData_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).toSimplexData.pullback (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ) =
      (strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).toSimplexData := by
  have ho : ((strictRawModuleTensorDoubleConeSimplex A X P Q c).toSimplexData.pullback
      (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ)).obj =
      (strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj := by
    funext i
    exact strictRawModuleTensorDoubleConeSimplex_obj_reindex A X P Q c θ i
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext ho
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise ho
  intro I a b k hI ha hb hk
  by_cases hbl : b = Fin.last (m + 2)
  · by_cases hi : Set.InjOn (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ) (I : Set (Fin (m + 3)))
    · exact strictRawModuleTensorDoubleConeSimplex_pullback_hom_terminal_injOn
        A X P Q c θ I a b k hI ha hb hk hbl hi
    · exact strictRawModuleTensorDoubleConeSimplex_pullback_hom_terminal_not_inj
        A X P Q c θ I a b k hI ha hb hk hbl hi
  · have hfront := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData
      (strictRawModuleTensorDoubleConeSimplex_pullback_front A X P Q c θ)
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data] at hfront
    exact moduleSimplexData_hom_heq_of_front_eq A (dgAlgebraCategory A ((assocForget A).obj X)) _ _ hfront I a b k hI ha hb hk hbl

lemma strictRawModuleTensorDoubleConeSimplex_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ) =
      strictRawModuleTensorDoubleConeSimplex A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact strictRawModuleTensorDoubleConeData_pullback_map A X P Q c θ

end SerrePositivity.EInfinity.BarrattEccles
