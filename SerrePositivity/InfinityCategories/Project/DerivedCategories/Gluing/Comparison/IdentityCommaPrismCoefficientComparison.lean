module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityCommaPrismInactiveComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.ComplexScalarHEqComparison

/-! 二端と primitive の照合は、同じ実 augmentation prism の全係数の照合を与える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) (T : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R T]
  {x y : E} {x' y' : T} {n : ℕ}
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)) _⦋n⦌)
  (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R T T (DGFunctor.id T))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T x') (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T y')) _⦋n⦌)
  (q : _root_.SerrePositivity.DifferentialGraded.homObject R E x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R T x' y')
  (hsrc : ∀ J k hJ hk, q.f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaSourceComponent R E s J k hJ hk) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaSourceComponent R T t J k hJ hk)
  (hrep : ∀ J k hJ hk, q.f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent R E s J k hJ hk) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent R T t J k hJ hk)
  (hprim : ∀ J p hJ hp,
    q.f (p - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R T T (DGFunctor.id T)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T x') (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T y') p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData t).component J p hJ hp))

include hsrc hrep hprim in
lemma dgGluingIdentityCommaPrism_component_post_compare
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    q.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component
        J k hJ hk) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R T t β)).component J k hJ hk := by
  have hf : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases hf (β (J.min' hJ)) with hzero | hone
  · by_cases hactive : ∃ h₂ : 2 ≤ J.card, β (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J h₂) = 1
    · obtain ⟨h₂, hsecond⟩ := hactive
      have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexMap_scalar_heq q (by omega) _ _ _ _ _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_correction R E s β J h₂ k hk hzero hsecond)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_correction R T t β J h₂ k hk hzero hsecond)
        (hprim (J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty h₂))) (k + 1) _ _)
      rw [map_sub, hrep] at hd
      simpa only [sub_add_cancel] using congrArg
        (fun z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x' y' k =>
          z + _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent R T t J k hJ hk) hd
    · have hsecond : ∀ h₂ : 2 ≤ J.card, β (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.second J h₂) ≠ 1 := by
        simpa only [not_exists] using hactive
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_inactive R E s β J k hJ hk hzero hsecond,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_inactive R T t β J k hJ hk hzero hsecond]
      exact hrep J k hJ hk
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_one R E s J k hJ hk β hone,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_one R T t J k hJ hk β hone]
    exact hsrc J k hJ hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
