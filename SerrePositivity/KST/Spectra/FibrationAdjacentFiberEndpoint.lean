module

public import SerrePositivity.KST.Spectra.FibrationAdjacentEndpoint
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Pullbacks.FiberSimplexLifting

/-!
概要：比較ホーンの終点の一致を、全空間でなく指定した fiber 内で証明する。
方針：比較ホモトピー全体の射影が定数であることから RelStruct を fiber へ持ち上げる。
規約：全空間への包含がホモトピー群に単射であるとは仮定しない。
使われ方：Goerss–Jardine I §8。連結射の交換式の終点の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.AdjacentLiftComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B Y Z : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 1) (p.app _ e)}
  (U : E.PtSimplex (n + 1) e) (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
  {y : Y _⦋0⦌} (h : E ⟶ Y) (hpoint : h.app _ e = y)
  (hV : V.map ≫ h = SSet.const y)
  (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
  (hface : ∀ j, j ≠ Fin.last (n + 2) → stdSimplex.δ j ≫ φ = face U V j)
  (r : Y ⟶ Z) (hr : (φ ≫ h) ≫ r = SSet.const (r.app _ y))

include hr hface

/-- 概要：元の持ち上げの終点の射影は基点で定数。
方針：比較単体の最後から二番目の面を取り、全体の定数射影を制限する。
規約：射影が定数なホモトピー全体から導く。
使われ方：Goerss–Jardine I §8。fiber の中での始点の代表。 -/
lemma sourceEndpoint_comp : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex h hpoint U).map ≫ r = SSet.const (r.app _ y) := by
  have hf := hface (Fin.last (n + 1)).castSucc (Fin.castSucc_ne_last _)
  simp only [face, Fin.val_castSucc, Fin.val_last] at hf
  rw [ite_eq_right (by omega), ite_true] at hf
  change (U.map ≫ h) ≫ r = _
  rw [← hf, Category.assoc, Category.assoc, ← Category.assoc φ h r, hr, comp_const]

include hV in
/-- 概要：出力の終点の射影も基点で定数。
方針：比較単体の最後の面へ全体の定数射影を制限する。
規約：終点代表は構成済みの endpointSimplex。
使われ方：Goerss–Jardine I §8。fiber の中での終点の代表。 -/
lemma targetEndpoint_comp :
    (endpointSimplex U V h hpoint hV φ hface).map ≫ r = SSet.const (r.app _ y) := by
  change (stdSimplex.δ (Fin.last (n + 2)) ≫ φ ≫ h) ≫ r = _
  rw [Category.assoc, Category.assoc, ← Category.assoc φ h r, hr, comp_const]

include hV in
/-- 概要：出力と元の持ち上げの終点のホモトピー類は fiber 内で一致する。
方針：全体の定数射影により endpointRel を fiber へ持ち上げ、商へ送る。
規約：r の fibration 性だけで fiber の Kan 性を得る。
使われ方：Goerss–Jardine I §8。交換式を正しい fiber の群で閉じる。 -/
lemma fiberEndpoint_class [Fibration r] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex r y
      (endpointSimplex U V h hpoint hV φ hface)
      (targetEndpoint_comp U V h hpoint hV φ hface r hr)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftSimplex r y (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex h hpoint U)
      (sourceEndpoint_comp U V h hpoint φ hface r hr)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftRelStruct r y
    (sourceEndpoint_comp U V h hpoint φ hface r hr)
    (targetEndpoint_comp U V h hpoint hV φ hface r hr)
    (endpointRel U V h hpoint hV φ hface) hr)).symm

end
end SerrePositivity.KST.Spectra.AdjacentLiftComparison
