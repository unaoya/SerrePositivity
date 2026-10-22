module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismChainInputComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedPrismFamily

/-! 同じ二射影・primitive を保持する二鎖入力の実 augmentation prism 全体を比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded CochainComplex HomComplex
open DGNerve DGNerve.PinchedHom SSet MonoidalCategory
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
lemma dgGluingIdentityCommaPrism_chain_input_compare :
    (Δ[1] ◁ pinchedHomChainMap φ) ≫ dgGluingIdentityCommaPinchedPrism R E x y ≫
        pinchedHomChainMap q =
      (Δ[1] ◁ pinchedHomChainMap ψ) ≫ dgGluingIdentityCommaPinchedPrism R T x' y' := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro z
  apply (linearEquiv x' y' n).injective
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (toLinearData (pinchedHomChainMapSimplex q
      (dgGluingIdentityCommaPinchedPrismSimplex R E (pinchedHomChainMapSimplex φ z.2)
        (stdSimplex.objEquiv z.1).toOrderHom))).component J k hJ hk =
    (toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R T
      (pinchedHomChainMapSimplex ψ z.2) (stdSimplex.objEquiv z.1).toOrderHom)).component J k hJ hk
  rw [dgGluingPinchedChainMapSimplex_component]
  exact dgGluingIdentityCommaPrism_chain_input_component_compare R C E T a b x y x' y'
    φ ψ q hsrc hrep hprim z.2 (stdSimplex.objEquiv z.1).toOrderHom J k hJ hk

end SerrePositivity.InfinityCategories
