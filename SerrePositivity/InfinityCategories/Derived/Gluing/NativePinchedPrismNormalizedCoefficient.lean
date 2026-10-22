module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismOneCoefficient
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismMixedComparison

/-! 元 prism の全係数を同じ係数 Hom へ移す。相一だけ実 augmentation で前合成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom HomologicalComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

abbrev dgGluingNativePinchedPrismCoefficient (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :=
  (dgGluingNativePinchedPrismSimplex R C D M s β).hom (withLast J)
    (J.min' hJ).castSucc (Fin.last (n + 1)) k (two_withLast hJ) (min_withLast hJ _)
    (max_withLast J _) (by rw [card_withLast]; omega)

def dgGluingNativePrismNormalizedCoefficient (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom R (representable R X.left) (M.rightAt Y.right) k :=
  if hb : β (J.min' hJ) = 1 then
    (eHomWhiskerRight (Complex R) (dgGluingAugmentation R C D M X)
      (ForgetEnrichment.of (Complex R) (M.rightAt Y.right))).f k
      (gradedHomTransport (dgGluingNativePinchedPrism_source_one R C D M s β _ hb)
        (dgGluingNativePinchedPrism_target R C D M s β) rfl
        (dgGluingNativePinchedPrismCoefficient R C D M s β J k hJ hk))
  else
    gradedHomTransport (dgGluingNativePinchedPrism_source_zero R C D M s β _ (by omega))
      (dgGluingNativePinchedPrism_target R C D M s β) rfl
      (dgGluingNativePinchedPrismCoefficient R C D M s β J k hJ hk)

lemma dgGluingNativePrismNormalizedCoefficient_value
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    dgGluingNativePrismNormalizedCoefficient R C D M s β J k hJ hk =
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k
        (dgGluingNativeCoefficientPrismValue R C D M s β J k hJ hk) := by
  by_cases hb : β (J.min' hJ) = 1
  · rw [dgGluingNativePrismNormalizedCoefficient, dite_eq_left hb,
      dgGluingNativeCoefficientPrismValue, ite_eq_left hb]
    have hc := gradedHomTransport_eq_of_heq
      (dgGluingNativePinchedPrism_source_one R C D M s β _ hb)
      (dgGluingNativePinchedPrism_target R C D M s β) rfl _ _
      (dgGluingNativePinchedPrism_one_coefficient R C D M s β J k hJ hk hb)
    rw [hc]
    exact (ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (dgGluingRightAction_yoneda_inverse R C D M X Y) k)
        ((dgGluingRightHomMap R C D M X Y).f k ((toLinearData s).component J k hJ hk))).symm
  · rw [dgGluingNativePrismNormalizedCoefficient, dite_eq_right hb,
      dgGluingNativeCoefficientPrismValue, ite_eq_right hb]
    exact gradedHomTransport_eq_of_heq
      (dgGluingNativePinchedPrism_source_zero R C D M s β _ (by omega))
      (dgGluingNativePinchedPrism_target R C D M s β) rfl _ _
      (dgGluingNativePinchedPrism_mixed_value R C D M s β J k hJ hk (by omega))

lemma dgGluingNativePrismNormalizedCoefficient_comparison
    (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    dgGluingNativePrismNormalizedCoefficient R C D M s
        (SSet.stdSimplex.objEquiv β).toOrderHom J k hJ hk =
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k
        ((complexUnitHomIso (M.value X.left Y.right)).inv.f k
          ((toLinearData ((dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
            (Opposite.op ⦋n⦌)
            (β, (pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).component J k hJ hk)) :=
  (dgGluingNativePrismNormalizedCoefficient_value R C D M s _ J k hJ hk).trans
    (congrArg (fun z => (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k z)
      (dgGluingNativeCoefficientPrism_model_component R C D M s β J k hJ hk).symm)

end SerrePositivity.InfinityCategories
