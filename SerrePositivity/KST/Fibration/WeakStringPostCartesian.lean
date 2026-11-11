module
public import SerrePositivity.KST.Fibration.WeakStringFirstFacePullback
public import SerrePositivity.KST.SConstruction.SimplicialCartesianNaturality

/-! # 元の Verdier 包含の全 W 列後合成の全単体的な面条件 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 元の全ての面の自然性四角形は、全正反復で homotopy pullback。 -/
theorem weakStringMultiPostcomp_face_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r n : ℕ) (j : Fin (n + 2)) :
    IsHomotopyPullback (CommSq.mk ((weakStringMultiPostcomp i q (r + 1)).naturality
      (SimplexCategory.δ j).op)) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · exact weakStringMultiPostcomp_firstFace_homotopyPullback h r n
  · apply weakStringMultiPostcomp_headPreserving_homotopyPullback h r
      (SimplexCategory.δ k.succ)
    exact Fin.succ_succAbove_zero k

/-- 元の全ての退化の自然性四角形は、全正反復で homotopy pullback。 -/
theorem weakStringMultiPostcomp_degeneracy_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r n : ℕ) (j : Fin (n + 1)) :
    IsHomotopyPullback (CommSq.mk ((weakStringMultiPostcomp i q (r + 1)).naturality
      (SimplexCategory.σ j).op)) := by
  apply weakStringMultiPostcomp_headPreserving_homotopyPullback h r (SimplexCategory.σ j)
  simp [SimplexCategory.σ]

/-- 元の全 W 列の Verdier 包含による後合成は、全正反復で全単体的に homotopy-cartesian。 -/
theorem weakStringMultiPostcomp_homotopyPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r : ℕ) {d e : SimplexCategory} (θ : d ⟶ e) :
    IsHomotopyPullback (CommSq.mk ((weakStringMultiPostcomp i q (r + 1)).naturality
      θ.op)) :=
  simplicialNaturality_homotopyPullback_of_head (weakStringMultiPostcomp i q (r + 1))
    (fun θ hθ => weakStringMultiPostcomp_headPreserving_homotopyPullback h r θ hθ) θ

end SerrePositivity.KST.Fibration
