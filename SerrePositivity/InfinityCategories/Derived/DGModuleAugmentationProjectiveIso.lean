module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationClosedEdge
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveModules
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionHomotopy
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
/-!
概要：元の dg 関手の出力が射影的なら、同じ augmentation 全体は実関手同型。
方針：同じ実辺の準同型性をホモトピー同値へ昇格し、全ホモトピーを可逆にする。
規約：射影性は元の出力へ明示する。使われ方：一般出力分解と既存 graph tensor の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (hF : ∀ x, dgModuleProjectiveProperty R E (F.obj x))
include hF
/-- 元の出力が射影的なら、同じ augmentation ホモトピーの各頂点辺は可逆。 -/
lemma dgModuleAugmentationNerveHomotopy_projective_vertex_isInvertible
    (X : DGModuleFunctorResolutionObject R C E F) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge
      (dgModuleAugmentationNerveHomotopy R C E F) (Simplex.vertex X)).toTruncated := by
  have := dgModuleEdge_isIso_of_homotopy R E X.augmentation
    (moduleHomotopicallyProjective_quasiIso_isIso_homotopy R E
      (dgSemifreeModule_isProjective R E X.replacement) (hF X.source) X.augmentation X.quasiIso)
  have he : IsInvertibleEdge (X := dgModuleNerve R E)
      (dgClosedEdge R (RightModule R E) X.augmentation) :=
    (edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge R E X.augmentation).toTruncated)
  have hm := he.map (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
    (RightModule R E)))
  apply (isInvertibleEdge_congr (dgModuleAugmentationNerveHomotopy_vertex_edge R C E F X)).mpr
  exact (isInvertibleEdge_congr (dgClosedEdge_map R (RightModule R E)
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))
      X.augmentation)).mp hm
/-- 同じ全単体 augmentation の実関手同型。 -/
def dgModuleAugmentationProjectiveIso :
    FunctorIso (dgNerve.map (dgModuleAugmentationSourceLift R C E F))
      (dgNerve.map (dgModuleAugmentationTargetLift R C E F)) :=
  functorIsoOfPointwiseInvertibleHomotopy (dgModuleAugmentationNerveHomotopy R C E F) (by
    intro s
    obtain ⟨X, rfl⟩ := Simplex.vertexEquiv.symm.surjective s
    exact dgModuleAugmentationNerveHomotopy_projective_vertex_isInvertible R C E F hF X)
/-- 同じ厳密切断に沿った、実出力分解と元の関手の全関手比較。 -/
def dgModuleOutputResolutionProjectiveIso :
    FunctorIso
      (dgModuleOutputResolutionInfinity R C E F ≫
        dgNerve.map (dgModuleOutputInclusionLift.{u, max (u + 1) v, v} R E))
      (dgNerve.map (dgModuleOutputOriginalLift R C E F)) := by
  have e := (dgModuleAugmentationProjectiveIso R C E F hF).precomp
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  rw [dgModuleOutputResolution_replacement, dgModuleOutputResolution_original] at e
  exact e
end SerrePositivity.InfinityCategories
