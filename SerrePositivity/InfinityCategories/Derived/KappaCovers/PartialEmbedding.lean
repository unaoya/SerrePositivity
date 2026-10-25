module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.PartialTower
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.FilteredEmbedding

/-!
概要：部分 cell 列の余極限を、元の標準 resolution へ次数ごと単射で入れる。
方針：各有限段の単射性を filtered 余極限からの比較射へ延ばす。
規約：native 比較は不要。
使われ方：D-8 d の関手等式と余極限の等式反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) (s : Set (DGKappaResolutionLabel R D M))
  (hs : ∀ a ∈ s, dgKappaResolutionDependencies R D M a ⊆ s)

lemma dgKappaPartialResolutionInclusion_degreewiseMono (x : D) (q : ℤ) :
    Mono (((moduleEvaluation R D x).map (dgKappaPartialResolutionInclusion R D M s hs)).f q) := by
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  exact dgKappaModuleFilteredCoconeDesc_degreewiseMono R D (J := ℕ)
    (dgKappaPartialResolutionDiagram R D M s hs) (dgKappaPartialResolutionCocone R D M s hs)
    (dgKappaPartialResolutionStageToCandidate_degreewiseMono R D M s hs) x q

lemma dgKappaPartialResolutionInclusion_mono :
    Mono (dgKappaPartialResolutionInclusion R D M s hs) :=
  dgKappaModuleMap_mono R D _ (dgKappaPartialResolutionInclusion_degreewiseMono R D M s hs)

end SerrePositivity.InfinityCategories
