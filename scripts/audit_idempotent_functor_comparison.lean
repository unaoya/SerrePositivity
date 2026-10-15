import SerrePositivity.PerfectComplex.InvolutionBaseChange
import SerrePositivity.PerfectComplex.CubicActionBaseChange
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
  {K : CochainComplex (ModuleCat.{u} R) ℤ}

section Involution
variable [Invertible (2 : R)] [Invertible (2 : S)] (t : CochainInvolution K)

-- The new common comparison has exactly the old hom and inv, not only isomorphic objects.
example : CochainInvolution.positiveBaseChangeIso φ t =
    CochainIdempotent.imageFunctorIso
        ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)) t.positive ≪≫
      CochainIdempotent.imageIso _ _ (Iso.refl _) (by
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        rw [Category.comp_id, Category.id_comp]
        exact CochainInvolution.baseChange_positive_map φ t) := rfl

example : CochainInvolution.negativeBaseChangeIso φ t =
    CochainIdempotent.imageFunctorIso
        ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)) t.negative ≪≫
      CochainIdempotent.imageIso _ _ (Iso.refl _) (by
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        rw [Category.comp_id, Category.id_comp]
        exact CochainInvolution.baseChange_negative_map φ t) := rfl
end Involution

section Cubic
variable [Invertible (3 : R)] [Invertible (3 : S)]
example (τ : CochainCubicAction K) (t : R) (ht : t ^ 3 = 1) (j : Fin 3) :
    CochainCubicAction.characterBaseChangeIso φ τ t ht j =
      CochainIdempotent.imageFunctorIso
          ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ))
          (τ.characterProjector t ht j) ≪≫
        CochainIdempotent.imageIso _ _ (Iso.refl _) (by
          change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
          rw [Category.comp_id, Category.id_comp]
          simpa only [CochainIdempotent.mapFunctor, CochainCubicAction.characterProjector,
            CochainCubicAction.projector, cubicCharacter, map_pow] using
              CochainCubicAction.baseChange_projectorMap φ τ (cubicCharacter t j)) := rfl
end Cubic

assert_no_sorry SerrePositivity.CochainIdempotent.imageFunctorIsoOfMapEq
assert_no_sorry SerrePositivity.CochainIdempotent.imageFunctorIsoOfMapEq_hom_inclusion
assert_no_sorry SerrePositivity.CochainInvolution.positiveBaseChangeIso_hom_inclusion
assert_no_sorry SerrePositivity.CochainInvolution.negativeBaseChangeIso_hom_inclusion
assert_no_sorry SerrePositivity.CochainCubicAction.characterBaseChangeIso_hom_inclusion
#print axioms SerrePositivity.CochainIdempotent.imageFunctorIsoOfMapEq
#print axioms SerrePositivity.CochainCubicAction.characterBaseChangeIso
