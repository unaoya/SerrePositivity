module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationDescentTypedHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatHomRestrictionNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationDescentHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatComparisonNormalized
/-!
概要：元の指定比較 ξ の任意双加群射に対する自然性を証明する。
方針：同じ制限比較 ρ の四角形と実変形降下の自然性を接続する。
規約：同じ比較と射を保持し、可逆性を仮定しない。使われ方：κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
lemma dgRelativeKFlatKernelNerve_derivedIso_hom_naturality
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) hP).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E f hP hQ) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D Q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q) hQ).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_normalized,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_normalized]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationComparisonIso_hom_naturality_typed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatQuasiIsomorphismEdges R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy_vertex_mem R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_resolution_inverts R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_resolution_inverts R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q) hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E (BimoduleCategory.underlying R E D P) hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E (BimoduleCategory.underlying R E D Q) hQ)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D P) hP)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E (BimoduleCategory.underlying R E D Q) hQ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E f hP hQ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso_hom_square R D E f hP hQ)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
