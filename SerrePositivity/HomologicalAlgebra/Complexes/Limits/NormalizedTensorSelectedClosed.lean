module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementSelectedCochain
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：一点を選ぶ最上位普遍 cochain は元の Hom 複体の閉零元である。
方針：元の線形単体の微分方程式を使い、同じ最大点への移送を微分と両立させる。
規約：同じ選択 cochain を保つ。使われ方：実 cone の混合辺の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochain_closed {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochain A X Y c J 0 hJ (by omega)) = 0 := by
  let s := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y
    ((SimplexCategory.toCat.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelection J hJ)).toFunctor ⋙ c)
  have hd : 0 = 1 - ((Finset.univ : Finset (Fin (J.card - 1 + 1))).card : ℤ) := by
    simp [hc]
  have hz : s.val.rhs Finset.univ 0 hd = 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
    exact dite_eq_right (by simp [hc])
  exact (s.equation Finset.univ 0 Finset.univ_nonempty hd).trans hz

lemma normalizedTensorElementSelectedCochainAtMax_closed {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J 0 hJ (by omega)) =
      0 := by
  have hy : (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (J.max' hJ)) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj
        (c.obj ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1)))) :=
    (congrArg (fun i => (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelection_last J hJ)).symm
  have he : HEq (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J 0 hJ (by omega))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochain A X Y c J 0 hJ (by omega)) := cast_heq _ _
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) rfl hy rfl _ _ he
  exact eq_of_heq (hd.trans ((heq_of_eq
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochain_closed A X Y c J hJ hc)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) rfl hy rfl).symm))

end SerrePositivity.ComplexLimits
