module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismInactiveComponent
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexScalarHEqComparison

/-! 二端と primitive の照合は、同じ実 augmentation prism の全係数の照合を与える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) (T : Type w)
  [DGCategory R E] [DGCategory R T]
  {x y : E} {x' y' : T} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) _⦋n⦌)
  (t : (DGNerve.pinchedHom R (DGFunctorCommaObject R T T (DGFunctor.id T))
    (dgGluingIdentityCommaObject R T x') (dgGluingIdentityCommaObject R T y')) _⦋n⦌)
  (q : homObject R E x y ⟶ homObject R T x' y')
  (hsrc : ∀ J k hJ hk, q.f k (dgGluingIdentityCommaSourceComponent R E s J k hJ hk) =
    dgGluingIdentityCommaSourceComponent R T t J k hJ hk)
  (hrep : ∀ J k hJ hk, q.f k (dgGluingIdentityCommaReplacementComponent R E s J k hJ hk) =
    dgGluingIdentityCommaReplacementComponent R T t J k hJ hk)
  (hprim : ∀ J p hJ hp,
    q.f (p - 1) (dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
      (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) p
      ((toLinearData s).component J p hJ hp)) =
    dgCommaAugmentationHomotopyComponent R T T (DGFunctor.id T)
      (dgGluingIdentityCommaObject R T x') (dgGluingIdentityCommaObject R T y') p
      ((toLinearData t).component J p hJ hp))

include hsrc hrep hprim in
lemma dgGluingIdentityCommaPrism_component_post_compare
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    q.f k ((toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component
        J k hJ hk) =
      (toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R T t β)).component J k hJ hk := by
  have hf : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases hf (β (J.min' hJ)) with hzero | hone
  · by_cases hactive : ∃ h₂ : 2 ≤ J.card, β (second J h₂) = 1
    · obtain ⟨h₂, hsecond⟩ := hactive
      have hd := dgGluingComplexMap_scalar_heq q (by omega) _ _ _ _ _
        (dgGluingIdentityCommaPrism_component_correction R E s β J h₂ k hk hzero hsecond)
        (dgGluingIdentityCommaPrism_component_correction R T t β J h₂ k hk hzero hsecond)
        (hprim (J.erase (J.min' (Index.nonempty h₂))) (k + 1) _ _)
      rw [map_sub, hrep] at hd
      simpa only [sub_add_cancel] using congrArg
        (fun z : GradedHom R x' y' k =>
          z + dgGluingIdentityCommaReplacementComponent R T t J k hJ hk) hd
    · have hsecond : ∀ h₂ : 2 ≤ J.card, β (second J h₂) ≠ 1 := by
        simpa only [not_exists] using hactive
      rw [dgGluingIdentityCommaPrism_component_inactive R E s β J k hJ hk hzero hsecond,
        dgGluingIdentityCommaPrism_component_inactive R T t β J k hJ hk hzero hsecond]
      exact hrep J k hJ hk
  · rw [dgGluingIdentityCommaPrism_component_one R E s J k hJ hk β hone,
      dgGluingIdentityCommaPrism_component_one R T t J k hJ hk β hone]
    exact hsrc J k hJ hk

end SerrePositivity.InfinityCategories
