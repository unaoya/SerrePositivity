module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPinchedPrismMixedCoefficient
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedSimplex
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionComponents
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

/-! 任意 augmentation の実混合主項を、元 pinched Hom の replacement 射影の閉後合成へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)

lemma dgGluingCommaAugmentationComponent_heq {X Y : DGFunctorCommaObject R C E F}
    (h : X = Y) :
    HEq (dgCommaAugmentationComponent R C E F X).val
      (dgCommaAugmentationComponent R C E F Y).val := by
  cases h
  rfl

lemma dgGluingCommaPinchedPrismMain_linear
    {X Y : DGFunctorCommaObject R C E F} {n : ℕ}
    (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R C E F) X Y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq (dgGluingCommaPrismMainCoefficient R C E F s.val.toSimplexData
        (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (two_withLast hJ) (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega))
      ((dgClosedPostcomposition R E (x := X.replacement) Y.augmentation).f k
        (((dgCommaAugmentationSource R C E F).map X Y).f k
          ((toLinearData s).component J k hJ hk))) := by
  have hx := source_obj s (J.min' hJ)
  have hy := target_obj s
  have hh := dgGluingFunctor_map_component_heq (dgCommaAugmentationSource R C E F)
    hx hy k (toLinearData_component_heq s J k hJ hk).symm
  have hc := gradedHom_compose_heq
    (congrArg (fun Z : DGFunctorCommaObject R C E F => Z.replacement) hx)
    (congrArg (fun Z : DGFunctorCommaObject R C E F => Z.replacement) hy)
    (congrArg (fun Z : DGFunctorCommaObject R C E F => F.obj Z.source) hy)
    (p := k) (q := 0) (k := k) rfl rfl rfl _ _ _ _
    (dgGluingCommaAugmentationComponent_heq R C E F hy) hh (add_zero k) (add_zero k)
  exact hc.trans (heq_of_eq (dgClosedPostcomposition_f R E Y.augmentation k _).symm)

end SerrePositivity.InfinityCategories
