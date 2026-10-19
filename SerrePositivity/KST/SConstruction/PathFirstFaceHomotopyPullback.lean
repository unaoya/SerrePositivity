module
public import SerrePositivity.KST.SConstruction.ConnectedDiagramRetractions
public import SerrePositivity.KST.SConstruction.PathHeadHomotopyPullback
public import SerrePositivity.KST.SConstruction.MultiStageConnected

/-! # 経路境界の最初の面のホモトピー引き戻し
概要：元の経路境界の δ₀ の自然性四角形が全正有限反復実現後に homotopy pullback となる。
方針：σ₀ は先頭を保つため既証の面条件を満たし、基底の連結性と厳密な退縮で δ₀ を検出する。
規約：追加の面条件・行の Kan 性を仮定しない。使われ方：経路境界の全ての面条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 正の反復実現の最内側 S 図式の全ての行は連結。 -/
instance iteratedSRealizationDiagram_positive_isConnected (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) :
    SSet.IsConnected ((iteratedSRealizationDiagram (r + 1) X).obj d) :=
  multiDiagonalCoreSConstruction_isConnected r (sStableModel d.unop.len X)

/-- 経路境界の最初の面の元の自然性四角形は全正反復実現後に homotopy pullback。 -/
lemma iteratedPathBoundary_firstFace_homotopyPullback (r n : ℕ) (X : StableModel.{u}) :
    IsHomotopyPullback (CommSq.mk ((iteratedPathBoundary (r + 1) X).naturality
      (SimplexCategory.δ (0 : Fin (n + 2))).op)) := by
  have hsr : (SimplexCategory.σ (0 : Fin (n + 1))).op ≫
      (SimplexCategory.δ (0 : Fin (n + 2))).op = 𝟙 _ := by
    rw [← op_comp]
    change (SimplexCategory.δ (Fin.castSucc (0 : Fin (n + 1))) ≫
      SimplexCategory.σ (0 : Fin (n + 1))).op = _
    rw [SimplexCategory.δ_comp_σ_self, op_id]
  apply naturality_homotopyPullback_retraction_of_section
    (iteratedPathBoundary (r + 1) X) (SimplexCategory.σ (0 : Fin (n + 1))).op
    (SimplexCategory.δ (0 : Fin (n + 2))).op hsr (Classical.arbitrary _)
  exact iteratedPathBoundary_headPreserving_homotopyPullback r
    (SimplexCategory.σ (0 : Fin (n + 1))) (by rfl) X

end SerrePositivity.KST.SConstruction
