module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeMap
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeSimplex

/-!
概要：元の全次数の実 cone 単体は、退化を含む全作用素への自然性を持つ。
方針：同じ実データ全体の pullback の一致を単体の等式へ持ち上げる。
規約：元の対象・射・符号付き cochain を保持する。使われ方：大域 cone/prism の束ね。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeSimplex_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) =
      strictRawModuleTensorConeSimplex A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact strictRawModuleTensorConeData_pullback_map A X P Q c θ

end SerrePositivity.EInfinity.BarrattEccles
