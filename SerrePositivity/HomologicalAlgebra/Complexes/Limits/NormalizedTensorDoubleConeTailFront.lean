module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementAugmentedColumnMaps
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeMap
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoubleConeTailIndex

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementAugmentedColumn_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    Fin.castSuccOrderEmb.toOrderHom.monotone.functor ⋙
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c =
      c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y := by
  apply CategoryTheory.Functor.hext (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn_obj_castSucc A X Y c)
  intro i j f
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn_map_cast_cast A X Y c i j (leOfHom f)

lemma normalizedTensorElementAugmentedColumn_closed_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback]
  exact congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (F ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn_front A X Y c)

def normalizedTensorDoubleConeTail {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1) :=
  (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).pullback (_root_.SerrePositivity.ComplexLimits.doubleConeTailOrderHom n)

lemma normalizedTensorDoubleConeTail_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeTail A X Y c).pullback Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) := by
  have hindex : (_root_.SerrePositivity.ComplexLimits.doubleConeTailOrderHom n).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp (Fin.succOrderEmb (n + 1)).toOrderHom := by
    apply DFunLike.ext
    intro i
    exact _root_.SerrePositivity.ComplexLimits.doubleConeTailOrderHom_castSucc n i
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeTail, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_front, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex_tail]

end SerrePositivity.ComplexLimits
