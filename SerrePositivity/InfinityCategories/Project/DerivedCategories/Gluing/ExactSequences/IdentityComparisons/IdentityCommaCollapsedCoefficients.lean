module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityCommaCollapsedUnit

/-! 恒等 augmentation 頂点へ潰れた全次数係数は、相の選び方に依存しない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)

lemma dgGluingIdentityCommaCollapsedCoefficients
    {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R Q n) (α : Fin (m + 1) →o Fin (n + 1))
    (β γ : Fin (m + 1) →o Fin 2) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hab : α a = α b)
    (y : E) (hY : s.obj (α b) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E)
      (s.pullback α) β).hom I a b k hI ha hb hk)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E)
        (s.pullback α) γ).hom I a b k hI ha hb hk) := by
  have hle : a ≤ b := by rw [ha, hb]; exact (I.isLeast_min' _).2 (I.max'_mem _)
  by_cases hc : I.card = 2
  · have hk0 : k = 0 := by omega
    have hdegree : (0 : ℤ) = 2 - (I.card : ℤ) := by omega
    subst hk0
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaCollapsedPhase_unit R E s α β I a b hI ha hb hdegree hc hab
      y hY (β a) (β b) (β.monotone hle)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaCollapsedPhase_unit R E s α γ I a b hI ha hb hdegree hc hab
        y hY (γ a) (γ b) (γ.monotone hle)).symm
  · have hz (δ : Fin (m + 1) →o Fin 2) :
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E)
          (s.pullback α) δ).hom I a b k hI ha hb hk = 0 :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrismPhaseHom_collapsed_zero R E E (DGFunctor.id E) s α δ
        I a b k hI ha hb hk hab hc (δ a) (δ b) (δ.monotone hle)
    rw [hz, hz]
    have ho (δ : Fin (m + 1) →o Fin 2) (i : Fin (m + 1)) (hi : α i = α b) :
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) δ).obj i = y := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj _ _ (δ i) (s.obj (α i)) = y
      rw [hi, hY]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPhaseObj R E y (δ i)
    change HEq (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom R
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) β).obj a)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) β).obj b) k)
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom R
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) γ).obj a)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R E E (DGFunctor.id E) (s.pullback α) γ).obj b) k)
    rw [ho β a hab, ho β b rfl, ho γ a hab, ho γ b rfl]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
