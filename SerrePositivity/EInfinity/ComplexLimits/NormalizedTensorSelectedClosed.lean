module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementSelectedCochain
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochain_closed {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (normalizedTensorElementSelectedCochain A X Y c J 0 hJ (by omega)) = 0 := by
  let s := normalizedTensorElementUniversalLinear A X Y
    ((SimplexCategory.toCat.map (normalizedTensorElementSelection J hJ)).toFunctor ⋙ c)
  have hd : 0 = 1 - ((Finset.univ : Finset (Fin (J.card - 1 + 1))).card : ℤ) := by
    simp [hc]
  have hz : s.val.rhs Finset.univ 0 hd = 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
    exact dite_eq_right (by simp [hc])
  exact (s.equation Finset.univ 0 Finset.univ_nonempty hd).trans hz

lemma normalizedTensorElementSelectedCochainAtMax_closed {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (normalizedTensorElementSelectedCochainAtMax A X Y c J 0 hJ (by omega)) =
      0 := by
  have hy : (normalizedTensorElementDiagram A X Y).obj (c.obj (J.max' hJ)) =
      (normalizedTensorElementDiagram A X Y).obj
        (c.obj ((normalizedTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1)))) :=
    (congrArg (fun i => (normalizedTensorElementDiagram A X Y).obj (c.obj i))
      (normalizedTensorElementSelection_last J hJ)).symm
  have he : HEq (normalizedTensorElementSelectedCochainAtMax A X Y c J 0 hJ (by omega))
      (normalizedTensorElementSelectedCochain A X Y c J 0 hJ (by omega)) := cast_heq _ _
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) rfl hy rfl _ _ he
  exact eq_of_heq (hd.trans ((heq_of_eq
    (normalizedTensorElementSelectedCochain_closed A X Y c J hJ hc)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) rfl hy rfl).symm))

end SerrePositivity.EInfinity.ComplexLimits
