module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRelativeKFlatComparisonPath
/-!
概要：元の K-flat 比較 ξ を、同じ制限比較と実変形降下同型へ正規化する。
方針：同じ指定比較の射の回収式から同型全体の等式を得る。
規約：原 Hom の平坦性を追加しない。使われ方：ξ の双加群同型自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
/-- K-flat の通常 kernel 作用と同じ出力分解は、全準同型辺を反転する。 -/
lemma dgRelativeKFlatKernelNerve_resolution_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatQuasiIsomorphismEdges R D) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_resolution]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelToDerived_invertsQuasiIsomorphismEdges R D E P
/-- 元の指定比較 ξ は、同じ制限比較と実変形降下同型の合成。 -/
lemma dgRelativeKFlatKernelNerve_derivedIso_normalized :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P hP =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E P hP).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatQuasiIsomorphismEdges R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy_vertex_mem R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)
        (dgRelativeKFlatKernelNerve_resolution_inverts R D E P hP) := by
  apply Iso.ext
  rw [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso_hom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_normalized_hom R D E P hP
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
