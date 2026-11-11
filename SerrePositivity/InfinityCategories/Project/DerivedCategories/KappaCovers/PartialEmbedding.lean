module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialTower
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.FilteredEmbedding

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) (s : Set (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M))
  (hs : ∀ a ∈ s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDependencies R D M a ⊆ s)

lemma dgKappaPartialResolutionInclusion_degreewiseMono (x : D) (q : ℤ) :
    Mono (((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion R D M s hs)).f q) := by
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaModuleFilteredCoconeDesc_degreewiseMono R D (J := ℕ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionDiagram R D M s hs) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionCocone R D M s hs)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionStageToCandidate_degreewiseMono R D M s hs) x q

lemma dgKappaPartialResolutionInclusion_mono :
    Mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaPartialResolutionInclusion R D M s hs) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaModuleMap_mono R D _ (dgKappaPartialResolutionInclusion_degreewiseMono R D M s hs)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
