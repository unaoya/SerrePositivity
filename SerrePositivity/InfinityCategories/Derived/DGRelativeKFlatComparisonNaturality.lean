module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatRestrictionNaturality
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatComparisonNormalized
public import SerrePositivity.InfinityCategories.Derived.DeformationDescentNaturality
/-!
概要：K-flat の元の指定導来比較 ξ と双加群同型の作用の自然性を証明する。
方針：同じ制限比較 ρ の四角形と実変形降下比較の自然性を合成する。
規約：指定値・全関手同型を保ち、原 Hom の平坦性を追加しない。
使われ方：元の導来合成子 κ の五角・単位 coherence の移送。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の指定比較 ξ は、同じ双加群同型の導来作用と K-flat 作用に自然。 -/
lemma dgRelativeKFlatKernelNerve_derivedIso_bimodule_naturality
    {P Q : BimoduleCategory R E D} (e : P ≅ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    dgRelativeKFlatKernelNerve_derivedIso R D E (BimoduleCategory.underlying R E D P) hP ≪≫
      (dgRelativeKFlatKernelBimoduleIso R D E e hP hQ).postcomp
        (dgRelativeKFlatResolution R E) =
    (dgKernelDerivedInfinity_bimoduleIso R D E e).precomp (dgRelativeKFlatResolution R D) ≪≫
      dgRelativeKFlatKernelNerve_derivedIso R D E (BimoduleCategory.underlying R E D Q) hQ := by
  rw [dgRelativeKFlatKernelNerve_derivedIso_normalized,
    dgRelativeKFlatKernelNerve_derivedIso_normalized]
  exact deformationComparisonIso_naturality (dgRelativeKFlatResolution R D)
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
    (dgKernelDerivedInfinity_bimoduleIso R D E e)
    ((dgRelativeKFlatKernelBimoduleIso R D E e hP hQ).postcomp (dgRelativeKFlatResolution R E))
    (dgRelativeKFlatKernelRestrictionNerveIso_bimodule_square R D E e hP hQ)
end
end SerrePositivity.InfinityCategories
