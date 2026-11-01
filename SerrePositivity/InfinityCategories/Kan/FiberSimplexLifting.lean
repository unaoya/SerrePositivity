module

public import SerrePositivity.InfinityCategories.Kan.FibrationBoundary
public import SerrePositivity.InfinityCategories.Kan.HomotopyGroups

/-!
概要：fiber に入る単体とホモトピーを、fiber 内の代表へ厳密に持ち上げる。
方針：pullback の普遍性で持ち上げ、包含後の各面を比較する。
規約：射影が実際に定数である単体とホモトピーだけを扱う。
使われ方：Goerss–Jardine I §8。path の比較ホモトピーを fiber の中で保持する。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.KanFiber

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
    (KanFiber p (p.app _ e)).PtSimplex n (fiberPoint p e) where
  map := fiberLift p _ s.map hs
  comm := by
    apply fiber_hom_ext p (p.app _ e)
    simpa only [Category.assoc, fiberLift_ι, Subcomplex.ofSimplex_ι, comp_const,
      const_comp, SSet.const_app, fiberι_point] using s.comm

/-- fiber の単体の持ち上げを包含すると元の単体に戻る。 -/
@[reassoc (attr := simp)]
lemma liftSimplex_ι {n : ℕ} (s : E.PtSimplex n e)
    (hs : s.map ≫ p = SSet.const (p.app _ e)) :
    (liftSimplex p e s hs).map ≫ fiberι p (p.app _ e) = s.map := fiberLift_ι p (p.app _ e) s.map hs

/-- 概要：fiber に入る RelStruct は fiber 内の RelStruct へ持ち上がる。
方針：ホモトピーの射を pullback へ持ち上げ、指定二面と定数面を包含で照合する。
規約：ホモトピー全体の射影が定数であることを明示する。
使われ方：Goerss–Jardine I §8。全空間の一致を fiber 内の一致へ誤って移さない。 -/
def liftRelStruct {n : ℕ} {s t : E.PtSimplex n e} {i : Fin (n + 1)}
    (hs : s.map ≫ p = SSet.const (p.app _ e))
    (ht : t.map ≫ p = SSet.const (p.app _ e)) (r : PtSimplex.RelStruct s t i)
    (hr : r.map ≫ p = SSet.const (p.app _ e)) :
    PtSimplex.RelStruct (liftSimplex p e s hs) (liftSimplex p e t ht) i where
  map := fiberLift p _ r.map hr
  δ_castSucc_map := by
    apply fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, fiberLift_ι, liftSimplex_ι, r.δ_castSucc_map]
  δ_succ_map := by
    apply fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, fiberLift_ι, liftSimplex_ι, r.δ_succ_map]
  δ_map_of_lt j hj := by
    apply fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, fiberLift_ι, r.δ_map_of_lt j hj, const_comp, fiberι_point]
  δ_map_of_gt j hj := by
    apply fiber_hom_ext p (p.app _ e)
    simp only [Category.assoc, fiberLift_ι, r.δ_map_of_gt j hj, const_comp, fiberι_point]

end
end SerrePositivity.KST.Spectra.KanFiber
