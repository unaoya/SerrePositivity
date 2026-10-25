module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ProjectiveBarNativeCocone
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeProjectiveEquivalence

/-!
概要：射影的頂点を持つ bar の擬同型を、同じ射影的模型の頂点同型へ戻す。
方針：二端点の射影性でホモトピー同型にし、充満包含で反映する。
規約：全加群 nerve 内での擬同型の可逆性は仮定しない。
使われ方：C1 の擬同型比較を C2 の native 頂点比較へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgProjectiveModuleNerve R D)

lemma dgProjectiveBarNativeCocone_image :
    fullInclusionCocone R (RightModule R D) (dgModuleProjectiveProperty R D)
        (dgProjectiveBarNativeCocone R D G) =
      dgCoherentBarNormalizedNativeCoconeUnconditional R D (dgProjectiveBarDiagram R D G) := by
  apply Subtype.ext
  exact fullInclusionLift_comp R (RightModule R D) (dgModuleProjectiveProperty R D) _
    (dgProjectiveBarNativeCocone_vertices R D G)

def dgProjectiveBarNativeCocone_vertexIso (N : ProjectiveDGModules R D)
    (f : ForgetEnrichment.of (Complex R)
        (dgCoherentBarNormalizedModuleUnconditional R D (dgProjectiveBarDiagram R D G)) ⟶
      ForgetEnrichment.of (Complex R) N.val)
    (hf : moduleQuasiIso R D f) :
    VertexIso (dgProjectiveBarNativeCocone R D G).vertex (Simplex.vertex N) := by
  let i := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
    (dgModuleProjectiveProperty R D))
  have h₀ : i.app (Opposite.op ⦋0⦌) (dgProjectiveBarNativeCocone R D G).vertex =
      Simplex.vertex (dgCoherentBarNormalizedModuleUnconditional R D
        (dgProjectiveBarDiagram R D G)) := by
    have h := congrArg JoinCocone.vertex (dgProjectiveBarNativeCocone_image R D G)
    exact h.trans (dgCoherentBarNormalizedNativeCocone_vertex R D _ _)
  have h₁ : i.app (Opposite.op ⦋0⦌) (Simplex.vertex N) = Simplex.vertex N.val :=
    dgFunctorNerve_vertex _ N
  have := dgModuleEdge_isIso_of_homotopy R D f
    (moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
      (dgCoherentBarNormalizedModule_homotopicallyProjective R D _
        (dgProjectiveBarDiagram_vertices R D G)) N.property f hf)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (dgModuleEdge R D f).toTruncated) :=
    (edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge R D f).toTruncated)
  let e : VertexIso (i.app (Opposite.op ⦋0⦌) (dgProjectiveBarNativeCocone R D G).vertex)
      (i.app (Opposite.op ⦋0⦌) (Simplex.vertex N)) :=
    eqToIso (congrArg SSet.HomotopyCategory.mk h₀) ≪≫
      asIso (SSet.Truncated.HomotopyCategory.homMk (dgModuleEdge R D f).toTruncated) ≪≫
        eqToIso (congrArg SSet.HomotopyCategory.mk h₁.symm)
  exact (dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R D)
    (dgModuleProjectiveProperty R D)).toHoFullyFaithful.preimageIso e

end SerrePositivity.InfinityCategories
