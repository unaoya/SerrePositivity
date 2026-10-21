module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompPointwiseInvertible
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInvertsQuasiIso
/-!
概要：同じ実ホモトピーの頂点辺を回収し、全関手射の可逆性へ接続する。
方針：元の閉射・実出力分解・関手空間の点ごとの判定を使う。
規約：出力の射影性と始域の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u
universe v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
open DGNerve.HomotopyComparison
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgModuleResolution_homotopy_isIso_of_quasiIso_vertex
    (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
    {X : SSet.{max (u + 1) v}} {f g : X ⟶ dgModuleNerve R E}
    (H : SSet.Homotopy f g)
    (hH : ∀ x : X _⦋0⦌, moduleQuasiIso R E
      (edgeClosed (simplicialHomotopyVertexEdge H x).toTruncated)) :
    IsIso (functorHomPostcomp f g
      (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))) := by
  apply functorHomPostcomp_homotopy_isIso_of_pointwise
  intro x
  apply dgModuleResolvedInfinity_invertsQuasiIso R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) (simplicialHomotopyVertexEdge H x).toTruncated
  exact hH x
end
end SerrePositivity.InfinityCategories
