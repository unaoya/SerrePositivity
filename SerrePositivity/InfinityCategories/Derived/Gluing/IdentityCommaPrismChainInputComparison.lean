module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismCoefficientComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedChainMapComponent

/-! 元鎖入力の二射影・全比較 cochain の等式から、実 prism 成分の後合成自然性を得る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded CochainComplex HomComplex
open DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E T : Type (max u v))
  [DGCategory R C] [DGCategory R E] [DGCategory R T]
  (a b : C) (x y : E) (x' y' : T)
  (φ : homObject R C a b ⟶ homObject R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
  (ψ : homObject R C a b ⟶ homObject R (DGFunctorCommaObject R T T (DGFunctor.id T))
    (dgGluingIdentityCommaObject R T x') (dgGluingIdentityCommaObject R T y'))
  (q : homObject R E x y ⟶ homObject R T x' y')
  (hsrc : φ ≫ (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map _ _ ≫ q =
    ψ ≫ (dgCommaAugmentationTarget R T T (DGFunctor.id T)).map _ _)
  (hrep : φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map _ _ ≫ q =
    ψ ≫ (dgCommaAugmentationSource R T T (DGFunctor.id T)).map _ _)
  (hprim : ((Cochain.ofHom φ).comp (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) =
    (Cochain.ofHom ψ).comp (dgFunctorCommaPrimitive R T T (DGFunctor.id T)
      (dgGluingIdentityCommaObject R T x') (dgGluingIdentityCommaObject R T y')) (zero_add (-1)))

include hsrc hrep hprim in
lemma dgGluingIdentityCommaPrism_chain_input_component_compare {n : ℕ}
    (s : (DGNerve.pinchedHom R C a b) _⦋n⦌) (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    q.f k ((toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E
          (pinchedHomChainMapSimplex φ s) β)).component J k hJ hk) =
      (toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R T
        (pinchedHomChainMapSimplex ψ s) β)).component J k hJ hk := by
  apply dgGluingIdentityCommaPrism_component_post_compare
  · intro J p hJ hp
    dsimp only [dgGluingIdentityCommaSourceComponent]
    rw [dgGluingPinchedChainMapSimplex_component, dgGluingPinchedChainMapSimplex_component]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hsrc p)
      ((toLinearData s).component J p hJ hp)
  · intro J p hJ hp
    dsimp only [dgGluingIdentityCommaReplacementComponent]
    rw [dgGluingPinchedChainMapSimplex_component, dgGluingPinchedChainMapSimplex_component]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hrep p)
      ((toLinearData s).component J p hJ hp)
  · intro J p hJ hp
    dsimp only [dgCommaAugmentationHomotopyComponent]
    rw [dgGluingPinchedChainMapSimplex_component, dgGluingPinchedChainMapSimplex_component]
    have hz := ConcreteCategory.congr_hom (Cochain.congr_v hprim p (p - 1) (by omega))
      ((toLinearData s).component J p hJ hp)
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      ModuleCat.comp_apply] at hz
    convert hz using 1

end SerrePositivity.InfinityCategories
