module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementAugmentedColumnMaps
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeMap
public import SerrePositivity.EInfinity.ComplexLimits.DoubleConeTailIndex

/-!
概要：通常終端付き列と二重 cone の末尾単体は、どちらも同じ元の全 frame 前面を持つ。
方針：実列の通常射を元の図式へ戻し、二重 cone の二つの前面制限を交換する。
規約：全高次成分を同じ通常閉単体へ回収する。使われ方：終端以外の全 cochain の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementAugmentedColumn_front {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    Fin.castSuccOrderEmb.toOrderHom.monotone.functor ⋙
      normalizedTensorElementAugmentedColumn A X Y c =
      c ⋙ normalizedTensorElementDiagram A X Y := by
  apply CategoryTheory.Functor.hext (normalizedTensorElementAugmentedColumn_obj_castSucc A X Y c)
  intro i j f
  exact normalizedTensorElementAugmentedColumn_map_cast_cast A X Y c i j (leOfHom f)

lemma normalizedTensorElementAugmentedColumn_closed_front {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (normalizedTensorElementAugmentedColumn A X Y c ⋙ complexToClosed A)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ normalizedTensorElementDiagram A X Y ⋙ complexToClosed A) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback]
  exact congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (F ⋙ complexToClosed A))
    (normalizedTensorElementAugmentedColumn_front A X Y c)

def normalizedTensorDoubleConeTail {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1) :=
  (normalizedTensorDoubleConeSimplex A X Y c).pullback (doubleConeTailOrderHom n)

lemma normalizedTensorDoubleConeTail_front {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorDoubleConeTail A X Y c).pullback Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ normalizedTensorElementDiagram A X Y ⋙ complexToClosed A) := by
  have hindex : (doubleConeTailOrderHom n).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp (Fin.succOrderEmb (n + 1)).toOrderHom := by
    apply DFunLike.ext
    intro i
    exact doubleConeTailOrderHom_castSucc n i
  rw [normalizedTensorDoubleConeTail, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    normalizedTensorDoubleConeSimplex_front, normalizedTensorConeSimplex_tail]

end SerrePositivity.EInfinity.ComplexLimits
