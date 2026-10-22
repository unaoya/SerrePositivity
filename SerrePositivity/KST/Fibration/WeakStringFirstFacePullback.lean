module
public import SerrePositivity.KST.Fibration.WeakStringHeadPullback
public import SerrePositivity.KST.SConstruction.ConnectedDiagramRetractions
public import SerrePositivity.KST.SConstruction.MultiStageConnected

/-! # 元の W 列後合成の第零面のホモトピー引き戻し -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 元の全 W 列の正の反復実現の各行は連結。 -/
instance weakStringMultiRealization_positive_isConnected {B C : StableCategory.{u}}
    (q : ExactMap B C) (r : ℕ) (d : SimplexCategoryᵒᵖ) :
    SSet.IsConnected ((weakStringMultiRealization q (r + 1)).obj d) :=
  multiDiagonalCoreSConstruction_isConnected r (weakStringModel q d.unop)

/-- Verdier 包含の元の後合成は、第零面でも全正有限反復で homotopy-cartesian。 -/
theorem weakStringMultiPostcomp_firstFace_homotopyPullback
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) (r n : ℕ) :
    IsHomotopyPullback (CommSq.mk ((weakStringMultiPostcomp i q (r + 1)).naturality
      (SimplexCategory.δ (0 : Fin (n + 2))).op)) := by
  have hsr : (SimplexCategory.σ (0 : Fin (n + 1))).op ≫
      (SimplexCategory.δ (0 : Fin (n + 2))).op = 𝟙 _ := by
    rw [← op_comp]
    change (SimplexCategory.δ (Fin.castSucc (0 : Fin (n + 1))) ≫
      SimplexCategory.σ (0 : Fin (n + 1))).op = _
    rw [SimplexCategory.δ_comp_σ_self, op_id]
  apply naturality_homotopyPullback_retraction_of_section
    (weakStringMultiPostcomp i q (r + 1)) (SimplexCategory.σ (0 : Fin (n + 1))).op
    (SimplexCategory.δ (0 : Fin (n + 2))).op hsr (Classical.arbitrary _)
  exact weakStringMultiPostcomp_headPreserving_homotopyPullback h r
    (SimplexCategory.σ (0 : Fin (n + 1))) (by rfl)

end SerrePositivity.KST.Fibration
