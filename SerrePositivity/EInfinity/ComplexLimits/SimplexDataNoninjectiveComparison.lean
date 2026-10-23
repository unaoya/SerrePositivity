module
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra
/-! 概要：非単射な引き戻しの同じ単位・零を比較する。
方針：二点と高次を分離。規約：元の端点。使われ方：三相自然性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

lemma simplexData_noninjective_pullback_hom_heq {m n : ℕ} (s t : SimplexData A D n)
    (θ : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hn : ¬ Set.InjOn θ (I : Set (Fin (m + 1))))
    (hx : s.obj (θ a) = t.obj (θ a)) (hy : s.obj (θ b) = t.obj (θ b)) :
    HEq ((s.pullback θ).hom I a b k hI ha hb hk)
      ((t.pullback θ).hom I a b k hI ha hb hk) := by
  by_cases hc : I.card = 2
  · have hu : ∀ {x y : D} (h : x = y),
        HEq (unitElement A x).val (unitElement A y).val := by
      intro x y h
      cases h
      rfl
    exact (s.pullback_hom_of_collapsed_pair θ I a b k hI ha hb hk hn hc).trans
      ((hu hy).trans (t.pullback_hom_of_collapsed_pair θ I a b k hI ha hb hk hn hc).symm)
  · rw [SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hn hc,
      SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hn hc]
    exact gradedHom_zero_heq hx hy rfl

end SerrePositivity.EInfinity.ComplexLimits
