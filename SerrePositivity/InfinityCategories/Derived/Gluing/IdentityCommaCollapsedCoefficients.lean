module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaCollapsedUnit

/-! 恒等 augmentation 頂点へ潰れた全次数係数は、相の選び方に依存しない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)

lemma dgGluingIdentityCommaCollapsedCoefficients
    {m n : ℕ} (s : SimplexData R Q n) (α : Fin (m + 1) →o Fin (n + 1))
    (β γ : Fin (m + 1) →o Fin 2) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hab : α a = α b)
    (y : E) (hY : s.obj (α b) = dgGluingIdentityCommaObject R E y) :
    HEq ((dgCommaAugmentationPrismData R E E (DGFunctor.id E)
      (s.pullback α) β).hom I a b k hI ha hb hk)
      ((dgCommaAugmentationPrismData R E E (DGFunctor.id E)
        (s.pullback α) γ).hom I a b k hI ha hb hk) := by
  have hle : a ≤ b := by rw [ha, hb]; exact (I.isLeast_min' _).2 (I.max'_mem _)
  by_cases hc : I.card = 2
  · have hk0 : k = 0 := by omega
    have hdegree : (0 : ℤ) = 2 - (I.card : ℤ) := by omega
    subst hk0
    exact (dgGluingIdentityCommaCollapsedPhase_unit R E s α β I a b hI ha hb hdegree hc hab
      y hY (β a) (β b) (β.monotone hle)).trans
      (dgGluingIdentityCommaCollapsedPhase_unit R E s α γ I a b hI ha hb hdegree hc hab
        y hY (γ a) (γ b) (γ.monotone hle)).symm
  · have hz (δ : Fin (m + 1) →o Fin 2) :
        (dgCommaAugmentationPrismData R E E (DGFunctor.id E)
          (s.pullback α) δ).hom I a b k hI ha hb hk = 0 :=
      dgGluingCommaPrismPhaseHom_collapsed_zero R E E (DGFunctor.id E) s α δ
        I a b k hI ha hb hk hab hc (δ a) (δ b) (δ.monotone hle)
    rw [hz, hz]
    have ho (δ : Fin (m + 1) →o Fin 2) (i : Fin (m + 1)) (hi : α i = α b) :
        (dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) δ).obj i = y := by
      change StrictNatTrans.phaseObj _ _ (δ i) (s.obj (α i)) = y
      rw [hi, hY]
      exact dgGluingIdentityCommaPhaseObj R E y (δ i)
    change HEq (0 : GradedHom R
      ((dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) β).obj a)
      ((dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) β).obj b) k)
      (0 : GradedHom R
        ((dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) γ).obj a)
        ((dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) γ).obj b) k)
    rw [ho β a hab, ho β b rfl, ho γ a hab, ho γ b rfl]

end SerrePositivity.InfinityCategories
