module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentBarProjective
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColimit
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveModules
public import SerrePositivity.InfinityCategories.Derived.FullColimitReflection
public import SerrePositivity.InfinityCategories.F1.Joins.JoinSmallness

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarCocone_vertices {K : SSet.{max (u + 1) v}}
    {p : K ⟶ dgNerve R (RightModule R D)} (c : JoinCocone p)
    (hp : ∀ s : K _⦋0⦌, dgModuleProjectiveProperty R D ((p.app _ s).obj 0))
    (hc : dgModuleProjectiveProperty R D (c.vertex.obj 0)) :
    ∀ z : (join K (Δ[0] : SSet.{max (u + 1) v})) _⦋0⦌,
      dgModuleProjectiveProperty R D ((c.val.app _ z).obj 0) := by
  intro z
  rcases join_vertices_covered K Δ[0] z with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · have h := congrArg (fun f : K ⟶ dgNerve R (RightModule R D) =>
        (f.app (Opposite.op ⦋0⦌) s).obj 0) c.property
    change (c.val.app _ ((joinInl K Δ[0]).app _ s)).obj 0 = _ at h
    rw [h]
    exact hp s
  · have he : joinInr K Δ[0] ≫ c.val = SSet.const c.vertex := by
      rw [← SSet.yonedaEquiv_symm_zero, JoinCocone.vertex_eq,
        Equiv.symm_apply_apply]
    have h := congrArg (fun f : (Δ[0] : SSet.{max (u + 1) v}) ⟶
        dgNerve R (RightModule R D) => (f.app (Opposite.op ⦋0⦌) s).obj 0) he
    change (c.val.app _ ((joinInr K Δ[0]).app _ s)).obj 0 = c.vertex.obj 0 at h
    rw [h]
    exact hc

variable {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgProjectiveModuleNerve R D)

abbrev dgProjectiveBarDiagram := G ≫ dgNerve.map
  (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D))

lemma dgProjectiveBarDiagram_vertices (s : I _⦋0⦌) :
    moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R)
      (coherentDiagramVertex (dgProjectiveBarDiagram R D G) s)) := by
  exact ((G.app _ (ULift.up s)).obj 0).property

lemma dgProjectiveBarNativeCocone_vertices :
    ∀ z : (join ((SSet.uliftFunctor.{max (u + 1) v, u}).obj I)
        (Δ[0] : SSet.{max (u + 1) v})) _⦋0⦌, dgModuleProjectiveProperty R D
      (((dgCoherentBarNormalizedNativeCoconeUnconditional R D
        (dgProjectiveBarDiagram R D G)).val.app _ z).obj 0) := by
  apply dgBarCocone_vertices
  · intro s
    exact ((G.app _ s).obj 0).property
  · rw [dgCoherentBarNormalizedNativeCocone_vertex]
    exact dgCoherentBarNormalizedModule_homotopicallyProjective R D _
      (dgProjectiveBarDiagram_vertices R D G)

def dgProjectiveBarNativeCocone : JoinCocone G := by
  let L := fullInclusionLift R (RightModule R D) (dgModuleProjectiveProperty R D)
    (dgCoherentBarNormalizedNativeCoconeUnconditional R D (dgProjectiveBarDiagram R D G)).val
    (dgProjectiveBarNativeCocone_vertices R D G)
  refine ⟨L, ?_⟩
  apply (cancel_mono (dgNerve.map
    (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)))).1
  rw [Category.assoc, fullInclusionLift_comp]
  exact (dgCoherentBarNormalizedNativeCoconeUnconditional R D
    (dgProjectiveBarDiagram R D G)).property

lemma dgProjectiveBarNativeCocone_isColimit :
    IsColimitCone (dgProjectiveBarNativeCocone R D G) := by
  apply isColimitCone_of_fullInclusion
  have he : fullInclusionCocone R (RightModule R D) (dgModuleProjectiveProperty R D)
      (dgProjectiveBarNativeCocone R D G) =
      dgCoherentBarNormalizedNativeCoconeUnconditional R D (dgProjectiveBarDiagram R D G) := by
    apply Subtype.ext
    exact fullInclusionLift_comp R (RightModule R D) (dgModuleProjectiveProperty R D) _
      (dgProjectiveBarNativeCocone_vertices R D G)
  rw [he]
  exact dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit R D _

end SerrePositivity.InfinityCategories
