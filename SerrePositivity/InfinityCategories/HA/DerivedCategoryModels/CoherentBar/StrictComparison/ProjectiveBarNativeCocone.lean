module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentBarProjective
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColimit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModules
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullColimitReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSmallness

/-!
概要：射影的模型の coherent 図式の正規化 bar 余錐を同じ模型へ戻す。
方針：全頂点と bar の射影性で充満部分圏へ持ち上げ、周囲の余極限性を反映する。
規約：全 HA 成分と native 余錐を保持する。
使われ方：工程 B と bar の射影性の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarCocone_vertices {K : SSet.{max (u + 1) v}}
    {p : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hp : ∀ s : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D ((p.app _ s).obj 0))
    (hc : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D (c.vertex.obj 0)) :
    ∀ z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{max (u + 1) v})) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D ((c.val.app _ z).obj 0) := by
  intro z
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_vertices_covered K Δ[0] z with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · have h := congrArg (fun f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D) =>
        (f.app (Opposite.op ⦋0⦌) s).obj 0) c.property
    change (c.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]).app _ s)).obj 0 = _ at h
    rw [h]
    exact hp s
  · have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ c.val = SSet.const c.vertex := by
      rw [← SSet.yonedaEquiv_symm_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq,
        Equiv.symm_apply_apply]
    have h := congrArg (fun f : (Δ[0] : SSet.{max (u + 1) v}) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D) => (f.app (Opposite.op ⦋0⦌) s).obj 0) he
    change (c.val.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]).app _ s)).obj 0 = c.vertex.obj 0 at h
    rw [h]
    exact hc

variable {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D)

abbrev dgProjectiveBarDiagram := G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
  (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))

lemma dgProjectiveBarDiagram_vertices (s : I _⦋0⦌) :
    _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex (dgProjectiveBarDiagram R D G) s)) := by
  exact ((G.app _ (ULift.up s)).obj 0).property

lemma dgProjectiveBarNativeCocone_vertices :
    ∀ z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{max (u + 1) v, u}).obj I)
        (Δ[0] : SSet.{max (u + 1) v})) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D
      (((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional R D
        (dgProjectiveBarDiagram R D G)).val.app _ z).obj 0) := by
  apply dgBarCocone_vertices
  · intro s
    exact ((G.app _ s).obj 0).property
  · rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCocone_vertex]
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedModule_homotopicallyProjective R D _
      (dgProjectiveBarDiagram_vertices R D G)

def dgProjectiveBarNativeCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G := by
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional R D (dgProjectiveBarDiagram R D G)).val
    (dgProjectiveBarNativeCocone_vertices R D G)
  refine ⟨L, ?_⟩
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
    (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)))).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp]
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional R D
    (dgProjectiveBarDiagram R D G)).property

lemma dgProjectiveBarNativeCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgProjectiveBarNativeCocone R D G) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isColimitCone_of_fullInclusion
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionCocone R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
      (dgProjectiveBarNativeCocone R D G) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional R D (dgProjectiveBarDiagram R D G) := by
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D) _
      (dgProjectiveBarNativeCocone_vertices R D G)
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit R D _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
