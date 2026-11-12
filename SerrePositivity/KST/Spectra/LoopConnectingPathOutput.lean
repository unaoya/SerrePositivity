module

public import SerrePositivity.KST.Spectra.LoopConnectingPathLift
public import SerrePositivity.KST.Spectra.LoopZeroPenultimate

/-!
概要：連結射の比較ホーンの出力を fiber 内の path 族とし、その逆符号を計算する。
方針：出力の面を Hom–fiber 同型で移し、最後から二番目の面の逆元公式へ適用する。
規約：基本群を含む全正次数で群の値を比較する。
使われ方：Goerss–Jardine I §8。二方向の連結射の代表の照合。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.LoopConnectingComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) {n : ℕ}
  {v : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right.PtSimplex (n + 1)
    ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint)}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint v)
  (φ : (Δ[n + 2] : SSet.{u}) ⟶ (basedPathSpace E).right)
  (hφ : φ ≫ (basedPathMap p).right =
    stdSimplex.σ (Fin.last (n)).castSucc ≫ (pathSimplex p (v := v)).map)

/-- 比較ホーンの最後の面を fiber 内の path として読む。 -/
def outputFamily : (Δ[n + 1] : SSet.{u}) ⟶ (basedPathSpace (pointedFiber p)).right :=
  AdjacentLiftComparison.output φ hφ ≫ (PointedMapping.fiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p).inv.right

/-- 概要：出力の path 族の非定数面は loop の連結射の境界の path 表示。
方針：比較ホーンの面の公式と、構成済みの境界 loop の厳密な同定を合成する。
規約：最後から二番目の面だけが非定数。
使われ方：Goerss–Jardine I §8。逆元公式への幾何的入力。 -/
lemma outputFamily_face (U : (basedPathSpace E).right.PtSimplex (n + 1)
    (basedPathSpace E).basepoint)
    (hface : ∀ j, j ≠ Fin.last (n + 2) →
      stdSimplex.δ j ≫ φ = AdjacentLiftComparison.face U (pathLift p V) j)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ outputFamily p φ hφ = if j.val = n then
      (boundaryLoop p V).map ≫ (PointedMapping.loopToPath (pointedFiber p)).right
      else SSet.const (basedPathSpace (pointedFiber p)).basepoint := by
  change stdSimplex.δ j ≫ AdjacentLiftComparison.output φ hφ ≫ _ = _
  rw [← Category.assoc, AdjacentLiftComparison.output_face U (pathLift p V) φ hφ hface]
  split_ifs
  · exact boundaryLoop_path p V
  · rw [const_comp]
    have hb : (pointedFiber (basedPathMap p)).basepoint =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (basedPathMap p).right (basedPathSpace E).basepoint :=
      PointedSimplicialSet.basepoint_ofVertex _ _
    exact congrArg (fun z ↦ SSet.const (X := (Δ[n] : SSet.{u})) z)
      ((congrArg ((PointedMapping.fiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p).inv.right.app _) hb.symm).trans
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (PointedMapping.fiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p).inv))

/-- 概要：出力の path の終点を全空間へ含めると、比較単体の最後の面の終点。
方針：Hom–fiber 同型と終点の射影式、および比較出力の包含式を合成する。
規約：fiber 内の終点の代表を厳密に追跡する。
使われ方：Goerss–Jardine I §8。終点の fiber 内の RelStruct との照合。 -/
@[reassoc]
lemma outputFamily_endpoint_include :
    (outputFamily p φ hφ ≫ (pathEndpoint (pointedFiber p)).right) ≫
        (pointedFiberι p).right =
      stdSimplex.δ (Fin.last (n + 2)) ≫ φ ≫ (pathEndpoint E).right := by
  have he := congrArg Under.Hom.right (PointedMapping.pathFiber_endpoint p)
  simp only [Under.comp_right] at he
  change (AdjacentLiftComparison.output φ hφ ≫
    (PointedMapping.fiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} p).inv.right ≫
      (pathEndpoint (pointedFiber p)).right) ≫ (pointedFiberι p).right = _
  simp only [Category.assoc]
  rw [he]
  change AdjacentLiftComparison.output φ hφ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (basedPathMap p).right
    ((basedPathMap p).right.app _ (basedPathSpace E).basepoint) ≫ (pathEndpoint E).right = _
  rw [← Category.assoc, AdjacentLiftComparison.output_ι]
  rfl

/-- 概要：出力の path の終点の族は境界定数単体。
方針：loop の path 表示の終点は定数なので、出力の全ての境界の終点が定数。
規約：基点は path の終点評価の像のまま保持する。
使われ方：Goerss–Jardine I §8。比較出力の終点の群の代表。 -/
def outputEndpointSimplex (U : (basedPathSpace E).right.PtSimplex (n + 1)
    (basedPathSpace E).basepoint)
    (hface : ∀ j, j ≠ Fin.last (n + 2) →
      stdSimplex.δ j ≫ φ = AdjacentLiftComparison.face U (pathLift p V) j) :
    (pointedFiber p).right.PtSimplex (n + 1)
      ((pathEndpoint (pointedFiber p)).right.app _
        (basedPathSpace (pointedFiber p)).basepoint) where
  map := outputFamily p φ hφ ≫ (pathEndpoint (pointedFiber p)).right
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    rw [← Category.assoc, outputFamily_face p V φ hφ U hface]
    split_ifs
    · rw [Category.assoc, PointedMapping.loopToPath_endpoint, comp_const, pathEndpoint_basepoint]
    · rw [const_comp]

/-- 概要：比較ホーンの境界 loop の高次群の値は、出力の終点の類の逆元。
方針：出力 path 族の唯一の非定数面に、全正次数の逆元公式を適用する。
規約：標準基点への移送以外の符号補正は行わない。
使われ方：Goerss–Jardine I §8。loop と連結射の交換の負符号。 -/
theorem output_boundary_inverse [Fibration p.right]
    {w : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right.PtSimplex (n + 2)
      ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint)}
    (W : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint w)
    (ψ : (Δ[n + 3] : SSet.{u}) ⟶ (basedPathSpace E).right)
    (hψ : ψ ≫ (basedPathMap p).right =
      stdSimplex.σ (Fin.last (n + 1)).castSucc ≫ (pathSimplex p (v := w)).map)
    (U : (basedPathSpace E).right.PtSimplex (n + 2) (basedPathSpace E).basepoint)
    (hface : ∀ j, j ≠ Fin.last (n + 3) →
      stdSimplex.δ j ≫ ψ = AdjacentLiftComparison.face U (pathLift p W) j) :
    loopPositiveHomotopyEquiv (pointedFiber p) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (boundaryLoop p W)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl (pointedFiber p).right)
        (pathEndpoint_basepoint (pointedFiber p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (outputEndpointSimplex p W ψ hψ U hface)))⁻¹ := by
  exact loopPositive_penultimate (pointedFiber p) n
    (outputEndpointSimplex p W ψ hψ U hface) (boundaryLoop p W) (outputFamily p ψ hψ)
    rfl (fun j ↦ by
      simpa only [Category.assoc, PointedMapping.loopToPath_fiber] using
        outputFamily_face p W ψ hψ U hface j)

/-- 概要：比較ホーンの零 loop 成分は、出力の終点の基本群の逆元を表す。
方針：零次元の非定数な loop 面に、零 loop の逆元公式を適用する。
規約：fiber の零次数は成分集合。逆元は終点の基本群で取る。
使われ方：Goerss–Jardine I §8。連結射の交換の基本段の符号。 -/
theorem output_zero_boundary_inverse [Fibration p.right]
    {w : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right.PtSimplex 1
      ((PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right.app _
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint)}
    (W : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint w)
    (ψ : (Δ[2] : SSet.{u}) ⟶ (basedPathSpace E).right)
    (hψ : ψ ≫ (basedPathMap p).right =
      stdSimplex.σ (0 : Fin 2) ≫ (pathSimplex p (v := w)).map)
    (U : (basedPathSpace E).right.PtSimplex 1 (basedPathSpace E).basepoint)
    (hface : ∀ j, j ≠ (2 : Fin 3) →
      stdSimplex.δ j ≫ ψ = AdjacentLiftComparison.face U (pathLift p W) j) :
    loopZeroHomotopyEquiv (pointedFiber p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (boundaryLoop p W)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl (pointedFiber p).right)
        (pathEndpoint_basepoint (pointedFiber p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (outputEndpointSimplex p W ψ hψ U hface)))⁻¹ := by
  exact loopZero_penultimate (pointedFiber p)
    (outputEndpointSimplex p W ψ hψ U hface) (boundaryLoop p W) (outputFamily p ψ hψ) rfl
    (by simpa only [Fin.val_zero, ite_true] using outputFamily_face p W ψ hψ U hface 0)
    (by simpa using outputFamily_face p W ψ hψ U hface 1)

end
end SerrePositivity.KST.Spectra.LoopConnectingComparison
