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
instance weakStringMultiRealization_positive_isConnected {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) (d : SimplexCategoryᵒᵖ) :
    SSet.IsConnected ((weakStringMultiRealization q (r + 1)).obj d) :=
  multiDiagonalCoreSConstruction_isConnected r (weakStringModel q d.unop)

/-- Verdier 包含の元の後合成は、第零面でも全正有限反復で homotopy-cartesian。 -/
theorem weakStringMultiPostcomp_firstFace_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r n : ℕ) :
    IsHomotopyPullback (CommSq.mk ((weakStringMultiPostcomp i q (r + 1)).naturality
      (SimplexCategory.δ (0 : Fin (n + 2))).op)) := by
  exact simplicialNaturality_homotopyPullback_of_head (weakStringMultiPostcomp i q (r + 1))
    (fun θ hθ => weakStringMultiPostcomp_headPreserving_homotopyPullback h r θ hθ)
    (SimplexCategory.δ (0 : Fin (n + 2)))

end SerrePositivity.KST.Fibration
