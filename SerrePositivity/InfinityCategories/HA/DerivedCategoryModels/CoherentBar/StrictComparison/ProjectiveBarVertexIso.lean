module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ProjectiveBarNativeCocone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeProjectiveEquivalence

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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D)

lemma dgProjectiveBarNativeCocone_image :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionCocone R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone R D G) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G) := by
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D) _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone_vertices R D G)

def dgProjectiveBarNativeCocone_vertexIso (N : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G)) ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N.val)
    (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R D f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone R D G).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))
  have h₀ : i.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone R D G).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G)) := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (dgProjectiveBarNativeCocone_image R D G)
    exact h.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCocone_vertex R D _ _)
  have h₁ : i.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N.val :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ N
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R D f
    (_root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedModule_homotopicallyProjective R D _
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram_vertices R D G)) N.property f hf)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D f).toTruncated) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D f).toTruncated)
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (i.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone R D G).vertex)
      (i.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) :=
    eqToIso (congrArg SSet.HomotopyCategory.mk h₀) ≪≫
      asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D f).toTruncated) ≪≫
        eqToIso (congrArg SSet.HomotopyCategory.mk h₁.symm)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).toHoFullyFaithful.preimageIso e

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
