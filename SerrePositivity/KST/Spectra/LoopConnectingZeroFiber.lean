module

public import SerrePositivity.KST.Spectra.LoopConnectingFiberEndpoint

/-!
概要：零 loop 成分の逆元公式を、共通 path の fiber 内の終点に移す。
方針：比較ホモトピー全体を fiber に入れ、二つの基点移送の単体の射が恒等であることを使う。
規約：loop の零次数は成分集合。終点側の基本群でだけ逆元を取る。
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

variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
  {v : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right.PtSimplex 1
    ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint)}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint v)
  (φ : (Δ[2] : SSet.{u}) ⟶ (basedPathSpace E).right)
  (hφ : φ ≫ (basedPathMap p).right =
    stdSimplex.σ (Fin.last 0).castSucc ≫ (pathSimplex p (v := v)).map)

include hφ

/-- 概要：比較ホモトピーの終点は全体として元の fiber に入る。
方針：path の終点の自然性を使い、底の loop の終点の定数性へ帰着する。
規約：ホモトピーの全体の射影が定数であることの厳密な等式。
使われ方：Goerss–Jardine I §8。fiber 内の RelStruct を構成するための条件。 -/
lemma zeroComparisonEndpoint_comp :
    (φ ≫ (pathEndpoint E).right) ≫ p.right = SSet.const (p.right.app _ E.basepoint) := by
  have hn := congrArg Under.Hom.right (pathEndpoint_natural p)
  simp only [Under.comp_right] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, hφ]
  simp only [pathSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex, Category.assoc,
    PointedMapping.loopToPath_endpoint, comp_const, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint]

/-- 概要：比較ホーンの境界 loop は元の fiber 内の U の終点の類の逆元を表す。
方針：逆元公式を標準 fiber 基点へ戻し、比較ホモトピーの fiber 内での類の一致を使う。
規約：境界 loop は零次元。終点の値は基本群で比較する。
使われ方：Goerss–Jardine I §8。代表による連結射の反可換性の計算。 -/
theorem boundaryLoop_zero_inverse_endpoint [Fibration p.right]
    (U : (basedPathSpace E).right.PtSimplex 1 (basedPathSpace E).basepoint)
    (hface : ∀ j, j ≠ Fin.last 2 →
      stdSimplex.δ j ≫ φ = AdjacentLiftComparison.face U (pathLift p V) j) :
    pointedFiberGroupEquiv p 0
        (loopZeroHomotopyEquiv (pointedFiber p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (boundaryLoop p V))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex p.right E.basepoint
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (pathEndpoint E).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) U)
        (AdjacentLiftComparison.sourceEndpoint_comp U (pathLift p V) (pathEndpoint E).right
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) φ hface p.right
          (zeroComparisonEndpoint_comp p φ hφ))))⁻¹ := by
  let t := AdjacentLiftComparison.endpointSimplex U (pathLift p V) (pathEndpoint E).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) (pathLift_endpoint p V) φ hface
  let ht := AdjacentLiftComparison.targetEndpoint_comp U (pathLift p V) (pathEndpoint E).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) (pathLift_endpoint p V) φ hface p.right
    (zeroComparisonEndpoint_comp p φ hφ)
  have he : pointedFiberGroupEquiv p 0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl (pointedFiber p).right)
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
  have hout := congrArg (pointedFiberGroupEquiv p 0)
    (output_zero_boundary_inverse p V φ hφ U hface)
  rw [map_inv, he] at hout
  have hc := AdjacentLiftComparison.fiberEndpoint_class U (pathLift p V) (pathEndpoint E).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (pathEndpoint E)) (pathLift_endpoint p V) φ hface p.right
    (zeroComparisonEndpoint_comp p φ hφ)
  exact hout.trans (congrArg Inv.inv hc)

omit hφ

/-- 概要：loop 側の境界と、同じ loop を覆う path の終点は逆元の関係にある。
方針：比較ホーンを実際に充填し、fiber 内の終点の比較と負符号の計算を適用する。
規約：零 loop 成分。比較ホーンの選択は結論に残さない。
使われ方：Goerss–Jardine I §8。二方向の連結射の代表による反可換性。 -/
theorem boundaryLoop_zero_inverse_common [Fibration p.right]
    (U : (basedPathSpace E).right.PtSimplex 1 (basedPathSpace E).basepoint)
    (hU : U.map ≫ (basedPathMap p).right = (pathSimplex p (v := v)).map) :
    pointedFiberGroupEquiv p 0
        (loopZeroHomotopyEquiv (pointedFiber p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (boundaryLoop p V))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (sourceFiberSimplex p U hU))⁻¹ := by
  have : Fibration (basedPathMap p).right := by
    change Fibration (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p).right
    infer_instance
  obtain ⟨φ, hface, hφ⟩ := AdjacentLiftComparison.exists_lift U (pathLift p V) hU
  exact boundaryLoop_zero_inverse_endpoint p V φ hφ U hface

end
end SerrePositivity.KST.Spectra.LoopConnectingComparison
