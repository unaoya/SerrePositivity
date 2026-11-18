module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeTail
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer

/-!
概要：実 cone の始頂点を含まない全ての成分が HA 方程式を満たす。
方針：元の frame 単体への実制限の一致から、同じ像の集合へ方程式を戻す。
規約：任意次数・全有限部分集合を保持する。使われ方：残る混合成分の方程式への還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_equation_without_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (h0 : (0 : Fin (n + 2)) ∉ I) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).Equation I := by
  have h := (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).equation_image_of_pullback
    (Fin.succOrderEmb (n + 1)).toOrderHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_tail A X Y c) (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) (Fin.succ_injective _).injOn
  have hi : (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).image (Fin.succOrderEmb (n + 1)).toOrderHom = I := by
    change (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).image Fin.succ = I
    rw [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.image_withoutFirst, Finset.erase_eq_of_notMem h0]
  simpa only [hi] using h

end SerrePositivity.ComplexLimits
