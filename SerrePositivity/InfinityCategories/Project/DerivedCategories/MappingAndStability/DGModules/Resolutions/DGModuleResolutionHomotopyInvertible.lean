module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPostcompPointwiseInvertible
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGModuleResolvedInvertsQuasiIso
/-!
概要：同じ実ホモトピーの頂点辺を回収し、全関手射の可逆性へ接続する。
方針：元の閉射・実出力分解・関手空間の点ごとの判定を使う。
規約：出力の射影性と始域の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u
universe v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed

open scoped _root_.Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgModuleResolution_homotopy_isIso_of_quasiIso_vertex
    (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
    {X : SSet.{max (u + 1) v}} {f g : X ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E}
    (H : SSet.Homotopy f g)
    (hH : ∀ x : X _⦋0⦌, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_homotopy_isIso_of_pointwise
  intro x
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_invertsQuasiIso R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated
  exact hH x
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
