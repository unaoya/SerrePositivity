module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismProjectionCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedChainMapComponent

/-! 元 Hom 鎖写像とその実比較 cochain の式から、明示 prism の全射影係数の定値性を得る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded CochainComplex HomComplex
open DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  (a b : C) (x y : E) {Q : Complex R}
  (φ : homObject R C a b ⟶ homObject R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
  (q : homObject R E x y ⟶ Q)
  (hpair : φ ≫ (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q =
    φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q)
  (hprim : ((Cochain.ofHom φ).comp (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) = 0)

include hpair hprim in
lemma dgGluingIdentityCommaPrism_input_component_post_zero {n : ℕ}
    (s : (DGNerve.pinchedHom R C a b) _⦋n⦌) (β : Fin (n + 1) →o Fin 2)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    q.f k ((toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E
          (pinchedHomChainMapSimplex φ s) β)).component J k hJ hk) =
      q.f k (dgGluingIdentityCommaReplacementComponent R E (pinchedHomChainMapSimplex φ s)
        J k hJ hk) := by
  apply dgGluingIdentityCommaPrism_component_post_zero
  · intro J p hJ hp
    dsimp only [dgCommaAugmentationHomotopyComponent]
    rw [dgGluingPinchedChainMapSimplex_component]
    have hz := ConcreteCategory.congr_hom (Cochain.congr_v hprim p (p - 1) (by omega))
      ((toLinearData s).component J p hJ hp)
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.zero_v, ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hz
    convert hz using 1
  · intro J p hJ hp
    dsimp only [dgGluingIdentityCommaSourceComponent, dgGluingIdentityCommaReplacementComponent]
    rw [dgGluingPinchedChainMapSimplex_component]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hpair p)
      ((toLinearData s).component J p hJ hp)

end SerrePositivity.InfinityCategories
