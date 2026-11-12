module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeEquation

/-!
概要：元の全単体列に X を前置した、全次数の実 cone 単体を構成する。
方針：同じ実生データと全 HA 方程式をまとめ、単射制限と元の通常末尾面を回収する。
規約：同じ元の対象・射・符号付き選択 cochain を保持する。
使われ方：全作用素への自然性と大域 cone/prism の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeSimplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1) where
  toSimplexData := normalizedTensorConeData A X Y c
  equation := normalizedTensorConeData_equation A X Y c

lemma normalizedTensorConeSimplex_data {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorConeSimplex A X Y c).toSimplexData = normalizedTensorConeData A X Y c := rfl

lemma normalizedTensorConeSimplex_pullback_injective {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (normalizedTensorConeSimplex A X Y c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) =
      normalizedTensorConeSimplex A X Y
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact normalizedTensorConeData_pullback_injective A X Y c e

lemma normalizedTensorConeSimplex_tail {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorConeSimplex A X Y c).pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ normalizedTensorElementDiagram A X Y ⋙ complexToClosed A) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact normalizedTensorConeData_tail A X Y c

end SerrePositivity.EInfinity.ComplexLimits
