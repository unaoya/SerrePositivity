module

public import SerrePositivity.KST.Spectra.NullHomotopyTriangleAdjustment
public import SerrePositivity.KST.Spectra.NullHomotopyEndpointLifting

/-!
概要：指定した二つの零ホモトピーを固定して、三角形と相対ホモトピーを持ち上げる。
方針：最後の面を欠く二辺のホーンを fibration で指定した downstairs の三角形へ持ち上げる。
規約：球面の両端を変えず、相対ホモトピーの射影も厳密に保つ。
使われ方：Goerss–Jardine VIII §1。核の障害の単射性の逐次工程。
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

/-- 指定した三角形を二つの零ホモトピーを固定して厳密に持ち上げる。 -/
theorem exists_lift {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {e : E _⦋0⦌} {b : B _⦋0⦌} (hb : p.app _ e = b) {n : ℕ}
    {s t : E.PtSimplex (n + 1) e} {u v : B.PtSimplex (n + 1) b}
    (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
    (S : PtSimplex.RelStruct .const t (Fin.last (n + 1)))
    (U : PtSimplex.RelStruct .const u (Fin.last (n + 1)))
    (V : PtSimplex.RelStruct .const v (Fin.last (n + 1)))
    (hR : R.map ≫ p = U.map) (hS : S.map ≫ p = V.map)
    (A : PtSimplex.RelStruct u v (Fin.last (n + 1)))
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ B)
    (hφ : ∀ j, stdSimplex.δ j ≫ φ = NullHomotopyTransport.triangleFace U A V j) :
    ∃ A' : PtSimplex.RelStruct s t (Fin.last (n + 1)),
      ∃ ψ : (Δ[n + 3] : SSet.{u}) ⟶ E,
        A'.map ≫ p = A.map ∧
        ∀ j, stdSimplex.δ j ≫ ψ = NullHomotopyTransport.triangleFace R A' S j := by
  have hc (j : Fin (n + 4)) (hj : j ≠ Fin.last (n + 3)) :
      face R S j ≫ p = stdSimplex.δ j ≫ φ := by
    rw [hφ]
    have hjv : j.val ≠ n + 3 := fun he ↦ hj (Fin.ext he)
    by_cases h₀ : j.val = n + 1
    · simp only [face, NullHomotopyTransport.triangleFace, h₀, ite_true, hR]
    by_cases h₁ : j.val = n + 2
    · simp only [face, NullHomotopyTransport.triangleFace, h₁,
        ite_eq_right (by omega : n + 2 ≠ n + 1), ite_true, hS]
    simp only [face, NullHomotopyTransport.triangleFace, h₀, h₁, hjv, ite_false,
      const_comp, hb]
  obtain ⟨ψ, hψ, hp⟩ := (compatible R S).exists_lift p φ hc
  refine ⟨relation R S ψ hψ, ψ, ?_, filler_face R S ψ hψ⟩
  change (stdSimplex.δ (Fin.last (n + 3)) ≫ ψ) ≫ p = A.map
  rw [Category.assoc, hp, hφ]
  simp only [NullHomotopyTransport.triangleFace, Fin.val_last,
    ite_eq_right (by omega : n + 3 ≠ n + 1),
    ite_eq_right (by omega : n + 3 ≠ n + 2), ite_true]

end
end SerrePositivity.KST.Spectra.NullHomotopyTriangle
