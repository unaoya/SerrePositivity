module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedAtMaxImage

/-!
概要：元の終端まで届く選択 cochain は、同じ普遍単体の成分そのものである。
方針：元の終端尾が恒等となるとき、輸送後の実後合成の像を回収する。
規約：元の端点等式を異種等号で保持する。
使われ方：cone の終端を含む混合削除成分の共通座標。
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

lemma normalizedTensorElementSelectedCochainAtMax_terminal {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hm : J.max' hJ = Fin.last n) :
    HEq (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk) := by
  have ht : ∀ (i : Fin (n + 1)) (h : i = Fin.last n)
      (v : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i)) k),
      HEq ((homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last i))))).f k v) v := by
    intro i h v
    subst i
    simp only [homOfLE_refl, CategoryTheory.Functor.map_id]
    have hi : homPostcompose X (𝟙 ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj
        (c.obj (Fin.last n)))) = 𝟙 _ := (homFunctor X).map_id _
    rw [hi]
    rfl
  exact (ht _ hm (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk)).symm.trans
    (heq_of_eq (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_image A X Y c J k hJ hk))

lemma normalizedTensorElementSelectedCochainAtMax_terminal_smul {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hm : J.max' hJ = Fin.last n) (r : ℤˣ) :
    HEq (r • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk)
      (r • (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y c).val.component J k hJ hk) := by
  have he := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_terminal A X Y c J k hJ hk hm
  have hs : ∀ (i j : Fin (n + 1)) (h : i = j)
      (a : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i)) k)
      (b : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj j)) k),
      HEq a b → HEq (r • a) (r • b) := by
    intro i j h a b hab
    subst j
    cases eq_of_heq hab
    rfl
  exact hs _ _ hm _ _ he

end SerrePositivity.ComplexLimits
