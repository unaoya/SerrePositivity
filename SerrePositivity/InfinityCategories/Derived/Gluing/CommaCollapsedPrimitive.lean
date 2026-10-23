module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismData
public import SerrePositivity.InfinityCategories.DGNerve.Reindex

/-! 単調写像で両端が潰れる全係数では、実 comma primitive は厳密に零。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)

lemma dgGluingCommaPrimitive_unitElement (X : DGFunctorCommaObject R C E F) :
    dgCommaAugmentationHomotopyComponent R C E F X X 0 (unitElement R X).val = 0 :=
  dgCommaAugmentationHomotopyComponent_unit R C E F X 0 _

lemma dgGluingCommaPrimitive_of_unit
    {X Y : DGFunctorCommaObject R C E F} {k : ℤ} (f : GradedHom R X Y k)
    (hXY : X = Y) (hk : k = 0) (hf : HEq f (unitElement R Y).val) :
    dgCommaAugmentationHomotopyComponent R C E F X Y k f = 0 := by
  cases hXY
  subst k
  rw [eq_of_heq hf]
  exact dgGluingCommaPrimitive_unitElement R C E F X

lemma dgGluingCommaPrimitive_pullback_collapsed
    {m n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hab : α a = α b) :
    dgCommaAugmentationHomotopyComponent R C E F
      ((s.pullback α).obj a) ((s.pullback α).obj b) k
      ((s.pullback α).hom I a b k hI ha hb hk) = 0 := by
  have haI : a ∈ I := ha ▸ I.min'_mem (Index.nonempty hI)
  have hbI : b ∈ I := hb ▸ I.max'_mem (Index.nonempty hI)
  have hlt : a < b := by
    rw [ha, hb]
    exact I.min'_lt_max'_of_card (by omega)
  have hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))) := by
    intro h
    exact (ne_of_lt hlt) (h haI hbI hab)
  by_cases hc : I.card = 2
  · exact dgGluingCommaPrimitive_of_unit R C E F _ (congrArg s.obj hab)
      (by omega) (SimplexData.pullback_hom_of_collapsed_pair s α I a b k hI ha hb hk hi hc)
  · rw [SimplexData.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc]
    exact map_zero (((dgFunctorCommaPrimitive R C E F _ _).v k (k - 1) (by omega)).hom)

lemma dgGluingCommaPrismCut_pullback_collapsed
    {m n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (m + 1))
    (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hα : α j = α b) :
    dgCommaAugmentationPrismCut R C E F (s.pullback α)
      I a b k hI ha hb hk j hj haj hjb = 0 := by
  dsimp only [dgCommaAugmentationPrismCut]
  rw [dgGluingCommaPrimitive_pullback_collapsed R C E F s α _ _ _ _ _ _ _ rfl hα,
    zero_compose, smul_zero]

end SerrePositivity.InfinityCategories
