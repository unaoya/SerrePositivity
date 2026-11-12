module

public import SerrePositivity.KST.Spectra.LoopConnectingFiberEndpoint

/-!
概要：path の相対ホーン充填から、既存 loop 群同型の逆の厳密な単体代表を得る。
方針：fiber の同型の逆で最後の面を戻し、基点だけの移送が単体の射を保つことを使う。
規約：充填の代表を別のホモトピー類の代表へ選び直さない。
使われ方：Goerss–Jardine I §8。連結射の代表計算を標準の群準同型へ移す。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SimplexBasepoint

/-- 基点の等式で境界条件だけを移し、単体の射はそのまま保つ。 -/
def rebase {X : SSet.{u}} {x y : X _⦋0⦌} (h : x = y) {m : ℕ}
    (s : X.PtSimplex m x) : X.PtSimplex m y where
  map := s.map
  comm := by subst y; exact s.comm

/-- 恒等射の群同型による基点移送は、射を変えない単体の移送と一致する。 -/
lemma group_mk {X : SSet.{u}} [KanComplex X] {x y : X _⦋0⦌} (h : x = y) {n : ℕ}
    (s : X.PtSimplex (n + 1) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (Iso.refl X) h (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (rebase h s) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) h (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
  congr 1

end SimplexBasepoint

namespace BoundaryLift

variable {Y : PointedSimplicialSet.{u}} {n : ℕ}
  {s : Y.right.PtSimplex (n + 2)
    ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)}
  (M : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pathEndpoint Y).right (basedPathSpace Y).basepoint s)

/-- path の充填の最後の面を loop の単体へ戻す。 -/
def loopSimplex : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right.PtSimplex (n + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (loopBasedPathFiberIso Y).inv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.iso_inverse_basepoint (loopBasedPathFiberIso Y) (loopBasedPathFiberIso_basepoint Y)) M.boundary

/-- loop の代表を path に含めると元の充填の最後の面へ戻る。 -/
@[reassoc]
lemma loopSimplex_toPath : (_root_.SerrePositivity.KST.Spectra.BoundaryLift.loopSimplex M).map ≫ (PointedMapping.loopToPath Y).right =
    stdSimplex.δ (Fin.last (n + 2)) ≫ M.map := by
  change (M.boundary.map ≫ (loopBasedPathFiberIso Y).inv) ≫ _ = _
  rw [← PointedMapping.loopToPath_fiber, Category.assoc, Iso.inv_hom_id_assoc]
  exact M.boundary_ι

/-- 概要：path の最後の面から得る loop の類は、底の類を既存 loop 同型で逆に移したもの。
方針：連結同型の単射性で比較し、任意の充填による連結射の代表公式を使う。
規約：標準基点への移送を式に保持する。
使われ方：Goerss–Jardine I §7–8。標準の loop 同型への代表の接続。 -/
lemma loopPositive_loopSimplex [KanComplex Y.right] :
    loopPositiveHomotopyEquiv Y n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.KST.Spectra.BoundaryLift.loopSimplex M)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl Y.right) (pathEndpoint_basepoint Y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) := by
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl Y.right) (pathEndpoint_basepoint Y)
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (loopBasedPathFiberIso Y)
      (loopBasedPathFiberIso_basepoint Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.KST.Spectra.BoundaryLift.loopSimplex M)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk M.boundary := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (loopBasedPathFiberIso Y).hom _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.KST.Spectra.BoundaryLift.loopSimplex M)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
    congr 1
    ext : 1
    simp only [loopSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : b.symm (loopPositiveHomotopyEquiv Y n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.KST.Spectra.BoundaryLift.loopSimplex M))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHomEquivOfTotalSubsingleton (pathEndpoint Y).right
      (basedPathSpace Y).basepoint n).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom (pathEndpoint Y).right (basedPathSpace Y).basepoint n _ = _
    rw [connecting_loopPositiveHomotopyEquiv, hf]
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting (pathEndpoint Y).right (basedPathSpace Y).basepoint (n + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq (pathEndpoint Y).right (basedPathSpace Y).basepoint M).symm
  have he' := congrArg b he
  simpa only [MulEquiv.apply_symm_apply] using he'

end BoundaryLift
end
end SerrePositivity.KST.Spectra
