module

public import SerrePositivity.KST.Spectra.LoopConnectingPathOutput

/-!
概要：loop の境界の逆元公式の終点を、元の fiber 内の持ち上げの終点へ戻す。
方針：比較ホモトピー全体を fiber に入れ、二つの基点移送の単体の射が恒等であることを使う。
規約：全正次数。全空間への包含のホモトピー群の単射性は使わない。
使われ方：Goerss–Jardine I §8。loop と連結射の交換式の代表による計算。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.LoopConnectingComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) {n : ℕ}
  {v : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right.PtSimplex (n + 2)
    ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint)}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint v)
  (φ : (Δ[n + 3] : SSet.{u}) ⟶ (basedPathSpace E).right)
  (hφ : φ ≫ (basedPathMap p).right =
    stdSimplex.σ (Fin.last (n + 1)).castSucc ≫ (pathSimplex p (v := v)).map)

include hφ

/-- 概要：比較ホモトピーの終点は全体として元の fiber に入る。
方針：path の終点の自然性を使い、底の loop の終点の定数性へ帰着する。
規約：ホモトピーの全体の射影が定数であることの厳密な等式。
使われ方：Goerss–Jardine I §8。fiber 内の RelStruct を構成するための条件。 -/
lemma comparisonEndpoint_comp :
    (φ ≫ (pathEndpoint E).right) ≫ p.right = SSet.const (p.right.app _ E.basepoint) := by
  have hn := congrArg Under.Hom.right (pathEndpoint_natural p)
  simp only [Under.comp_right] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, hφ]
  simp only [pathSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex, Category.assoc,
    PointedMapping.loopToPath_endpoint, comp_const, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint]

/-- 概要：比較ホーンの境界 loop は元の fiber 内の U の終点の類の逆元を表す。
方針：逆元公式を標準 fiber 基点へ戻し、比較ホモトピーの fiber 内での類の一致を使う。
規約：n=0 を含む。連結射の抽象的な交換式を仮定しない。
使われ方：Goerss–Jardine I §8。代表による連結射の反可換性の計算。 -/
theorem boundaryLoop_inverse_endpoint [Fibration p.right]
    (U : (basedPathSpace E).right.PtSimplex (n + 2) (basedPathSpace E).basepoint)
    (hface : ∀ j, j ≠ Fin.last (n + 3) →
      stdSimplex.δ j ≫ φ = AdjacentLiftComparison.face U (pathLift p V) j) :
    pointedFiberGroupEquiv p (n + 1)
        (loopPositiveHomotopyEquiv (pointedFiber p) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (boundaryLoop p V))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex p.right E.basepoint
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (pathEndpoint E).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) U)
        (AdjacentLiftComparison.sourceEndpoint_comp U (pathLift p V) (pathEndpoint E).right
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) φ hface p.right
          (comparisonEndpoint_comp p φ hφ))))⁻¹ := by
  let t := AdjacentLiftComparison.endpointSimplex U (pathLift p V) (pathEndpoint E).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) (pathLift_endpoint p V) φ hface
  let ht := AdjacentLiftComparison.targetEndpoint_comp U (pathLift p V) (pathEndpoint E).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) (pathLift_endpoint p V) φ hface p.right
    (comparisonEndpoint_comp p φ hφ)
  have he : pointedFiberGroupEquiv p (n + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl (pointedFiber p).right)
        (pathEndpoint_basepoint (pointedFiber p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (outputEndpointSimplex p V φ hφ U hface))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex p.right E.basepoint t ht) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 _) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 _) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (outputEndpointSimplex p V φ hφ U hface))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
    congr 1
    ext : 1
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p.right (p.right.app _ E.basepoint)
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex_ι]
    exact outputFamily_endpoint_include p φ hφ
  have hout := congrArg (pointedFiberGroupEquiv p (n + 1))
    (output_boundary_inverse p V φ hφ U hface)
  rw [map_inv, he] at hout
  have hc := AdjacentLiftComparison.fiberEndpoint_class U (pathLift p V) (pathEndpoint E).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) (pathLift_endpoint p V) φ hface p.right
    (comparisonEndpoint_comp p φ hφ)
  exact hout.trans (congrArg Inv.inv hc)

omit hφ
section Source
variable {m : ℕ}
  {w : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right.PtSimplex (m + 1)
    ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint)}
/-- 概要：底の loop を覆う path の境界定数単体の終点は fiber に入る。
方針：終点の自然性と底の loop の終点の定数性を使う。
規約：比較ホーンの選択を使わない。
使われ方：Goerss–Jardine I §8。連結射の元の終点の代表。 -/
lemma sourceEndpoint_comp_of_projection
    (U : (basedPathSpace E).right.PtSimplex (m + 1) (basedPathSpace E).basepoint)
    (hU : U.map ≫ (basedPathMap p).right = (pathSimplex p (v := w)).map) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (pathEndpoint E).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) U).map ≫ p.right =
        SSet.const (p.right.app _ E.basepoint) := by
  have hn := congrArg Under.Hom.right (pathEndpoint_natural p)
  simp only [Under.comp_right] at hn
  change (U.map ≫ (pathEndpoint E).right) ≫ p.right = _
  rw [Category.assoc, ← hn, ← Category.assoc, hU]
  simp only [pathSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex, Category.assoc,
    PointedMapping.loopToPath_endpoint, comp_const, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint]

/-- 底の loop を覆う path の境界定数単体の終点を fiber 内の単体にする。 -/
def sourceFiberSimplex
    (U : (basedPathSpace E).right.PtSimplex (m + 1) (basedPathSpace E).basepoint)
    (hU : U.map ≫ (basedPathMap p).right = (pathSimplex p (v := w)).map) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p.right (p.right.app _ E.basepoint)).PtSimplex (m + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex p.right E.basepoint
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (pathEndpoint E).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) U)
    (sourceEndpoint_comp_of_projection p U hU)

end Source

/-- 概要：loop 側の境界と、同じ loop を覆う path の終点は逆元の関係にある。
方針：比較ホーンを実際に充填し、fiber 内の終点の比較と負符号の計算を適用する。
規約：全正次数。比較ホーンの選択は結論に残さない。
使われ方：Goerss–Jardine I §8。二方向の連結射の代表による反可換性。 -/
theorem boundaryLoop_inverse_common [Fibration p.right]
    (U : (basedPathSpace E).right.PtSimplex (n + 2) (basedPathSpace E).basepoint)
    (hU : U.map ≫ (basedPathMap p).right = (pathSimplex p (v := v)).map) :
    pointedFiberGroupEquiv p (n + 1)
        (loopPositiveHomotopyEquiv (pointedFiber p) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (boundaryLoop p V))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (sourceFiberSimplex p U hU))⁻¹ := by
  have : Fibration (basedPathMap p).right := by
    change Fibration (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p).right
    infer_instance
  obtain ⟨φ, hface, hφ⟩ := AdjacentLiftComparison.exists_lift U (pathLift p V) hU
  exact boundaryLoop_inverse_endpoint p V φ hφ U hface

end
end SerrePositivity.KST.Spectra.LoopConnectingComparison
