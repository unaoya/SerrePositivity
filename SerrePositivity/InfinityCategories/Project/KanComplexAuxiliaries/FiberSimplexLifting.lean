module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups

/-!
概要：fiber に入る単体とホモトピーを、fiber 内の代表へ厳密に持ち上げる。
方針：pullback の普遍性で持ち上げ、包含後の各面を比較する。
規約：射影が実際に定数である単体とホモトピーだけを扱う。
使われ方：Goerss–Jardine I §8。path の比較ホモトピーを fiber の中で保持する。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.KanFiber
end SerrePositivity.KST.Spectra.KanFiber
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : SSet.{u}} (p : E ⟶ B) (e : E _⦋0⦌)

/-- 概要：fiber に入る境界定数単体を fiber 内の境界定数単体にする。
方針：単体の射を pullback へ持ち上げ、境界の定数性を包含で検出する。
規約：零次数を含む。Kan 性は不要。
使われ方：Goerss–Jardine I §8。fiber の群の代表の比較。 -/
def liftSimplex {n : ℕ} (s : E.PtSimplex n e)
    (hs : s.map ≫ p = SSet.const (p.app _ e)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) where
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p _ s.map hs
  comm := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, Subcomplex.ofSimplex_ι, comp_const,
      const_comp, SSet.const_app, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point] using s.comm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (liftSimplex)


/-- fiber の単体の持ち上げを包含すると元の単体に戻る。 -/
@[reassoc (attr := simp)]
lemma liftSimplex_ι {n : ℕ} (s : E.PtSimplex n e)
    (hs : s.map ≫ p = SSet.const (p.app _ e)) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex p e s hs).map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) = s.map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι p (p.app _ e) s.map hs

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (liftSimplex_ι)


/-- 概要：fiber に入る RelStruct は fiber 内の RelStruct へ持ち上がる。
方針：ホモトピーの射を pullback へ持ち上げ、指定二面と定数面を包含で照合する。
規約：ホモトピー全体の射影が定数であることを明示する。
使われ方：Goerss–Jardine I §8。全空間の一致を fiber 内の一致へ誤って移さない。 -/
def liftRelStruct {n : ℕ} {s t : E.PtSimplex n e} {i : Fin (n + 1)}
    (hs : s.map ≫ p = SSet.const (p.app _ e))
    (ht : t.map ≫ p = SSet.const (p.app _ e)) (r : PtSimplex.RelStruct s t i)
    (hr : r.map ≫ p = SSet.const (p.app _ e)) :
    PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex p e s hs) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex p e t ht) i where
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p _ r.map hr
  δ_castSucc_map := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex_ι, r.δ_castSucc_map]
  δ_succ_map := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex_ι, r.δ_succ_map]
  δ_map_of_lt j hj := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, r.δ_map_of_lt j hj, const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]
  δ_map_of_gt j hj := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, r.δ_map_of_gt j hj, const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (liftRelStruct)


end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftRelStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftRelStruct := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftRelStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftSimplex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftSimplex_ι := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftSimplex_ι_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex_ι_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftRelStruct._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftRelStruct._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftRelStruct._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftRelStruct._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftRelStruct._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftRelStruct._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftRelStruct._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftRelStruct._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftSimplex._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftSimplex._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanFiber.liftSimplex.congr_simp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex.congr_simp
