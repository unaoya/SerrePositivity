module
public import SerrePositivity.InfinityCategories.Derived.DeformationDescentTypedHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatHomRestrictionNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Derived.DeformationDescentHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatComparisonNormalized
/-!
概要：元の指定比較 ξ の任意双加群射に対する自然性を証明する。
方針：同じ制限比較 ρ の四角形と実変形降下の自然性を接続する。
規約：同じ比較と射を保持し、可逆性を仮定しない。使われ方：κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
lemma dgRelativeKFlatKernelNerve_derivedIso_hom_naturality
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    (dgRelativeKFlatKernelNerve_derivedIso R D E
      (BimoduleCategory.underlying R E D P) hP).hom ≫
      functorHomPostcomp
        (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
        (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ)
        (dgRelativeKFlatResolution R E)
        (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ) =
    functorHomPrecomp
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D Q))
      (dgRelativeKFlatResolution R D) ((dgKernelDerivedFunctorHomFunctor R D E).map f) ≫
      (dgRelativeKFlatKernelNerve_derivedIso R D E
        (BimoduleCategory.underlying R E D Q) hQ).hom := by
  rw [dgRelativeKFlatKernelNerve_derivedIso_normalized,
    dgRelativeKFlatKernelNerve_derivedIso_normalized]
  exact deformationComparisonIso_hom_naturality_typed (dgRelativeKFlatResolution R D)
    (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatQuasiIsomorphismEdges R D)
    (dgRelativeKFlatResolutionAugmentationHomotopy R D)
    (dgRelativeKFlatResolutionAugmentationHomotopy_vertex_mem R D)
    (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP ≫
      dgRelativeKFlatResolution R E)
    (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ ≫
      dgRelativeKFlatResolution R E)
    (dgRelativeKFlatKernelNerve_resolution_inverts R D E
      (BimoduleCategory.underlying R E D P) hP)
    (dgRelativeKFlatKernelNerve_resolution_inverts R D E
      (BimoduleCategory.underlying R E D Q) hQ)
    (dgRelativeKFlatKernelRestrictionNerveIso R D E (BimoduleCategory.underlying R E D P) hP)
    (dgRelativeKFlatKernelRestrictionNerveIso R D E (BimoduleCategory.underlying R E D Q) hQ)
    ((dgKernelDerivedFunctorHomFunctor R D E).map f)
    (functorHomPostcomp
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
      (dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ)
      (dgRelativeKFlatResolution R E) (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ))
    (dgRelativeKFlatKernelRestrictionNerveIso_hom_square R D E f hP hQ)
end
end SerrePositivity.InfinityCategories
