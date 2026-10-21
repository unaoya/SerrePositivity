module
public import SerrePositivity.InfinityCategories.Derived.DeformationRestrictionHomTransport
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelRestrictionNerve
/-!
概要：元の指定 K-flat 比較の射を、同じ制限比較と通常 K-flat 作用上の変形経路で表す。
方針：元の比較の射の式と、端点だけを揃えた同じ raw factor の HEq を使う。
規約：元の比較と実変形円柱の値を保持する。使われ方：合成比較の二経路の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
/-- 元の K-flat 比較の射は、同じ制限比較と同じ K-flat 変形円柱の類の合成。 -/
lemma dgRelativeKFlatKernelNerve_derivedIso_normalized_hom :
    (dgRelativeKFlatKernelNerve_derivedIso R D E P hP).hom =
      ((dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).precomp
        (dgRelativeKFlatResolution R D)).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (deformationFunctorDescentHomotopy (dgRelativeKFlatResolution R D)
          (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatResolutionAugmentationHomotopy R D)
          (dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatResolution R E))) := by
  exact eq_of_heq ((dgRelativeKFlatKernelNerve_derivedIso_hom_heq R D E P hP).trans
    (deformationRestrictionComparison_hom_heq (dgRelativeKFlatResolution R D)
      (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatResolutionAugmentationHomotopy R D)
      (dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P)
      (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP)
      (dgRelativeKFlatKernelComparisonIso R D E P)
      (dgRelativeKFlatKernelNerve_resolution R D E P hP).symm
      ((dgKernelDerivedInfinity_relativeKFlatRestrictionIso_heq R D E P).trans
        (dgRelativeKFlatKernelRestrictionNerveIso_heq R D E P hP).symm)
      (dgRelativeKFlatKernelComparisonIso_hom R D E P)))
end SerrePositivity.InfinityCategories
