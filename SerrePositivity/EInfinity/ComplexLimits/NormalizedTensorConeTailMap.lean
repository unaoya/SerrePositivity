module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeTail
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataComponents

/-!
概要：任意作用素による実 cone の通常成分を、同じ通常末尾面の制限として比較する。
方針：始点を除いた面の全自然性を使い、元の像の集合と端点へ成分を戻す。
規約：潰れた辺の単位分岐も元の通常 nerve の自然性で保持する。
使われ方：全作用素による cone データの pullback の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_pullback_tail_map {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((normalizedTensorConeData A X Y c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).pullback
      (Fin.succOrderEmb (m + 1)).toOrderHom =
      (normalizedTensorConeData A X Y ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).pullback
        (Fin.succOrderEmb (m + 1)).toOrderHom := by
  have hcomp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom).comp (Fin.succOrderEmb (m + 1)).toOrderHom =
      (Fin.succOrderEmb (n + 1)).toOrderHom.comp θ.toOrderHom := by
    ext i
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, hcomp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp,
    normalizedTensorConeData_tail, normalizedTensorConeData_tail]
  have hp := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback
    (c ⋙ normalizedTensorElementDiagram A X Y ⋙ complexToClosed A) θ.toOrderHom)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data] at hp
  exact hp.symm

end SerrePositivity.EInfinity.ComplexLimits
