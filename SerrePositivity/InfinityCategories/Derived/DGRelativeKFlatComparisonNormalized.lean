module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatComparisonPath
/-!
概要：元の K-flat 比較 ξ を、同じ制限比較と実変形降下同型へ正規化する。
方針：同じ指定比較の射の回収式から同型全体の等式を得る。
規約：原 Hom の平坦性を追加しない。使われ方：ξ の双加群同型自然性。
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
  (P : Bimodule R E D) (hP : Bimodule.rightRelativeKFlat R E D P)
/-- K-flat の通常 kernel 作用と同じ出力分解は、全準同型辺を反転する。 -/
lemma dgRelativeKFlatKernelNerve_resolution_inverts :
    InvertsEdges (dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatResolution R E)
      (dgRelativeKFlatQuasiIsomorphismEdges R D) := by
  rw [dgRelativeKFlatKernelNerve_resolution]
  exact dgRelativeKFlatKernelToDerived_invertsQuasiIsomorphismEdges R D E P
/-- 元の指定比較 ξ は、同じ制限比較と実変形降下同型の合成。 -/
lemma dgRelativeKFlatKernelNerve_derivedIso_normalized :
    dgRelativeKFlatKernelNerve_derivedIso R D E P hP =
      (dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).precomp
        (dgRelativeKFlatResolution R D) ≪≫
      deformationFunctorDescentIso (dgRelativeKFlatResolution R D)
        (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatQuasiIsomorphismEdges R D)
        (dgRelativeKFlatResolutionAugmentationHomotopy R D)
        (dgRelativeKFlatResolutionAugmentationHomotopy_vertex_mem R D)
        (dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatResolution R E)
        (dgRelativeKFlatKernelNerve_resolution_inverts R D E P hP) := by
  apply Iso.ext
  rw [Iso.trans_hom, deformationFunctorDescentIso_hom]
  exact dgRelativeKFlatKernelNerve_derivedIso_normalized_hom R D E P hP
end
end SerrePositivity.InfinityCategories
