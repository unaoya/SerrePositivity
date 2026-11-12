module

public import SerrePositivity.KST.Spectra.NullHomotopyTriangleLifting
public import SerrePositivity.KST.Spectra.TowerNullHomotopyObstruction

/-!
概要：隣接差が等しい二つの零ホモトピーの族の間で、相対ホモトピーを一段持ち上げる。
方針：移送による差の保存で右辺の差を零にし、三角形の交換と相対ホーン持ち上げを使う。
規約：次段の両球面と零ホモトピーを固定し、前段の相対ホモトピーを厳密に射影する。
使われ方：Goerss–Jardine VIII §1。核の障害の単射性の帰納工程。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.NullHomotopyTriangle
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NullHomotopyDifference NullHomotopyTransport

/-- 隣接する零ホモトピーの差が等しければ、三角形を保つ相対ホモトピーを持ち上げられる。 -/
theorem exists_step {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] [KanComplex B]
    {e : E _⦋0⦌} {b : B _⦋0⦌} (hb : p.app _ e = b) {n : ℕ}
    {s t : E.PtSimplex (n + 1) e} {u v : B.PtSimplex (n + 1) b}
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p hb s = u) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p hb t = v)
    (R : PtSimplex.RelStruct .const u (Fin.last (n + 1)))
    (S : PtSimplex.RelStruct .const v (Fin.last (n + 1)))
    (U : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (V : PtSimplex.RelStruct .const t (Fin.last (n + 1)))
    (A : PtSimplex.RelStruct u v (Fin.last (n + 1)))
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ B)
    (hφ : ∀ j, stdSimplex.δ j ≫ φ = triangleFace R A S j)
    (hd : difference R (mapNullTo p hb hs U) = difference S (mapNullTo p hb ht V)) :
    ∃ A' : PtSimplex.RelStruct s t (Fin.last (n + 1)),
      ∃ ψ : (Δ[n + 3] : SSet.{u}) ⟶ E,
        A'.map ≫ p = A.map ∧ ∀ j, stdSimplex.δ j ≫ ψ = triangleFace U A' V j := by
  let U' := mapNullTo p hb hs U
  let V' := mapNullTo p hb ht V
  let T := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport U' A
  have hdiff : difference S T = difference S V' := by
    exact (difference_eq_of_transport_fillers R U' A S T φ
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible U' A).liftOfKanComplex hφ
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.filler_face U' A)).symm.trans hd
  have hz : difference T V' = 1 := by
    have hprod := difference_comp S T V'
    rw [← hdiff] at hprod
    exact mul_right_cancel (hprod.trans (one_mul _).symm)
  obtain ⟨θ, hθ⟩ := exists_triangle_of_zero U' A V' hz
  exact exists_lift p hb U V U' V' (mapNullTo_map p hb hs U).symm
    (mapNullTo_map p hb ht V).symm A θ hθ

end
end SerrePositivity.KST.Spectra.NullHomotopyTriangle
