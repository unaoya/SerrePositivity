module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismProjectionInput
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaProjectionChainMaps
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedPrismFamily

/-! 補正を消す射影の下で、明示 augmentation prism は全単体・全時刻で定値になる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded CochainComplex HomComplex
open DGNerve DGNerve.PinchedHom SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  (a b : C) (x y : E) {T : Type (max u v)} [DGCategory R T] {x' y' : T}
  (φ : homObject R C a b ⟶ homObject R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
  (q : homObject R E x y ⟶ homObject R T x' y')
  (hpair : φ ≫ (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q =
    φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q)
  (hprim : ((Cochain.ofHom φ).comp (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) = 0)

include hpair hprim in
lemma dgGluingIdentityCommaPrism_input_post_zero :
    (Δ[1] ◁ pinchedHomChainMap φ) ≫ dgGluingIdentityCommaPinchedPrism R E x y ≫
        pinchedHomChainMap q =
      snd Δ[1] (DGNerve.pinchedHom R C a b) ≫ pinchedHomChainMap
        (φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map
          (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q) := by
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
    (toLinearData (pinchedHomChainMapSimplex _ z.2)).component J k hJ hk
  rw [dgGluingPinchedChainMapSimplex_component, dgGluingPinchedChainMapSimplex_component]
  have h := dgGluingIdentityCommaPrism_input_component_post_zero R C E a b x y φ q
    hpair hprim z.2 (stdSimplex.objEquiv z.1).toOrderHom J k hJ hk
  dsimp only [dgGluingIdentityCommaReplacementComponent] at h
  rw [dgGluingPinchedChainMapSimplex_component] at h
  exact h

end SerrePositivity.InfinityCategories
