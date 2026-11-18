module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementSelectedCochain
public import
  SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementUniversalAugmentationLinear
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexPostcomposeGraded

/-!
概要：元の最大点付き選択 cochain の正次成分は、同じ実 augmentation で零になる。
方針：添字等式による輸送を同じ後合成と両立させ、元の普遍線形成分の消滅を使う。
規約：元の augmentation・次数・符号を保つ。使われ方：大域 augmentation 三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorElementSelectedCochainAtMax_augmentation_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) :
    (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj (J.max' hJ)))).f k
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) = 0 := by
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i)) k),
      (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj j))).f k
        (cast (congrArg (fun z => (GradedHom A X
          ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj z)) k : Type u)) h) v) =
      (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj i))).f k v := by
    intro i j h v
    subst j
    rfl
  have hcard : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
  have hd : k = 1 - ((Finset.univ : Finset (Fin (J.card - 1 + 1))).card : ℤ) := by
    simpa only [Finset.card_univ, Fintype.card_fin, ← hcard] using hk
  have hz := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear_augmentation_zero A X Y
    ((SimplexCategory.toCat.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelection J hJ)).toFunctor ⋙ c)
    Finset.univ k (by simpa only [Finset.card_univ, Fintype.card_fin, ← hcard] using hc) hd
  exact (ht _ _ (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelection_last J hJ)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochain A X Y c J k hJ hk)).trans hz

lemma normalizedTensorElementSelectedCochainAtMax_augmentation_smul_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) (r : ℤˣ) :
    (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj (J.max' hJ)))).f k
      (r • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) = 0 := by
  simp only [Units.smul_def, map_zsmul,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_augmentation_zero A X Y c J k hJ hk hc,
    smul_zero]

lemma normalizedTensorElementSelectedCochainAtMax_augmentation_compose_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) (r : ℤˣ) :
    compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj (J.max' hJ))))).val
      (r • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk) (add_zero k) = 0 := by
  rw [_root_.SerrePositivity.ComplexLimits.complexPostcompose_graded]
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_augmentation_smul_zero A X Y c J k hJ hk hc r

end SerrePositivity.ComplexLimits
