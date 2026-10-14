module

public import SerrePositivity.KTheory.Adams.TensorSquareBaseChange
public import SerrePositivity.KTheory.Adams.TensorSquareEigenspaces
public import SerrePositivity.PerfectComplex.InvolutionBaseChange

/-! # Base change of the positive and negative tensor-square complexes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
variable [Invertible (2 : R)] [Invertible (2 : S)]
namespace Adams
variable (φ : R →+* S) (P : CochainComplex (ModuleCat.{u} R) ℤ)

def tensorSquarePositiveBaseChangeIso :
    baseChange φ (tensorSquarePositive P) ≅ tensorSquarePositive (baseChange φ P) :=
  CochainInvolution.positiveBaseChangeIso φ (tensorSquareInvolution P) ≪≫
    CochainIdempotent.imageIso _ _ (cochainTensorBaseChangeIso φ P P)
      (CochainInvolution.positive_naturality _ _ _ (tensorSquareBaseChangeIso_swap φ P))

def tensorSquareNegativeBaseChangeIso :
    baseChange φ (tensorSquareNegative P) ≅ tensorSquareNegative (baseChange φ P) :=
  CochainInvolution.negativeBaseChangeIso φ (tensorSquareInvolution P) ≪≫
    CochainIdempotent.imageIso _ _ (cochainTensorBaseChangeIso φ P P)
      (CochainInvolution.negative_naturality _ _ _ (tensorSquareBaseChangeIso_swap φ P))

@[reassoc]
lemma tensorSquarePositiveBaseChangeIso_hom_inclusion :
    (tensorSquarePositiveBaseChangeIso φ P).hom ≫
        (tensorSquarePositiveProjector (baseChange φ P)).inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
          (tensorSquarePositiveProjector P).inclusion ≫
        (cochainTensorBaseChangeIso φ P P).hom := by
  simp only [tensorSquarePositiveBaseChangeIso, Iso.trans_hom, Category.assoc,
    CochainIdempotent.imageIso_hom_inclusion,
    CochainInvolution.positiveBaseChangeIso_hom_inclusion_assoc]

@[reassoc]
lemma tensorSquareNegativeBaseChangeIso_hom_inclusion :
    (tensorSquareNegativeBaseChangeIso φ P).hom ≫
        (tensorSquareNegativeProjector (baseChange φ P)).inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
          (tensorSquareNegativeProjector P).inclusion ≫
        (cochainTensorBaseChangeIso φ P P).hom := by
  simp only [tensorSquareNegativeBaseChangeIso, Iso.trans_hom, Category.assoc,
    CochainIdempotent.imageIso_hom_inclusion,
    CochainInvolution.negativeBaseChangeIso_hom_inclusion_assoc]

end Adams
end SerrePositivity
