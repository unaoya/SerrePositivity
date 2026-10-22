module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePinchedPrismMixedValue
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCoefficientPrismValue

/-! 元 gluing augmentation の全実混合係数は、同じ元 Hom 上の明示 cochain prism の実係数に一致。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {X Y : DGGluingObject R C D M} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) _⦋n⦌)

lemma dgGluingNativePinchedPrism_mixed_comparison
    (β : (Δ[1] : SSet.{max u v w}) _⦋n⦌) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hβ : (SSet.stdSimplex.objEquiv β).toOrderHom (J.min' hJ) = 0) :
    HEq ((dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
        (s.val.map (dgGluingToComma R C D M))
        (pinchedPrismPhase (SSet.stdSimplex.objEquiv β).toOrderHom)).hom
        (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (two_withLast hJ) (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega))
      ((dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k
        ((complexUnitHomIso (M.value X.left Y.right)).inv.f k
          ((toLinearData ((dgGluingHomCoefficientAugmentationPrism R C D M X Y).app
            (Opposite.op ⦋n⦌)
            (β, (pinchedComplexModelIso X Y).hom.app (Opposite.op ⦋n⦌) s))).component
            J k hJ hk))) := by
  have hc := dgGluingNativePinchedPrism_mixed_value R C D M s
    (SSet.stdSimplex.objEquiv β).toOrderHom J k hJ hk hβ
  have hv := dgGluingNativeCoefficientPrism_model_component R C D M s β J k hJ hk
  rw [dgGluingNativeCoefficientPrismValue, ite_eq_right (by rw [hβ]; decide)] at hv
  exact hc.trans (heq_of_eq (congrArg
    (fun z => (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f k z) hv.symm))

end SerrePositivity.InfinityCategories
