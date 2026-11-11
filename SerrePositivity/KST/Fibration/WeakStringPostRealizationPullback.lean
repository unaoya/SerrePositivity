module
public import SerrePositivity.KST.Fibration.WeakStringPostCartesian
public import SerrePositivity.KST.Comparison.SegalRealizationComparison

/-! # 元の Verdier 包含の W 列の各行と全対角のホモトピー引き戻し -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 元の W 列後合成の各行から対角への実四角形は、全正反復で homotopy pullback。 -/
theorem weakStringMultiPostcomp_realization_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r n : ℕ) :
    IsHomotopyPullback (CommSq.mk
      (diagonalRowEvaluation_naturality (weakStringMultiPostcomp i q (r + 1)) n).symm) :=
  segalRealization_homotopyPullback (weakStringMultiPostcomp i q (r + 1))
    (fun _ _ θ _ => weakStringMultiPostcomp_homotopyPullback h r θ) n

end SerrePositivity.KST.Fibration
