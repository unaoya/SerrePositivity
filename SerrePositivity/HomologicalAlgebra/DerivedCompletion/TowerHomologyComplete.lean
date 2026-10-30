module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Milnor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulStageComplete

/-! # Koszul完備化候補のホモロジー加群の導来完備性

有限段のホモロジーの完備性を、直積・核・余核・拡大の閉性とMilnor列によって
候補の全次数のホモロジーへ移す。lim¹を消す必要はない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 二つの隣接次数の有限段ホモロジーが完備なら、ホモトピー逆極限の同じ次数も完備。 -/
theorem complexTowerHomology_isModuleComplete_of_stages (f : R)
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n) (i : ℤ)
    (hprev : ∀ n, IsModuleComplete R f ((K n).homology (i - 1)))
    (hsame : ∀ n, IsModuleComplete R f ((K n).homology i)) :
    IsModuleComplete R f ((complexTowerHomotopyLimit R K t).homology i) := by
  have hp := isModuleComplete_pi R f (fun n ↦ (K n).homology (i - 1)) hprev
  have hs := isModuleComplete_pi R f (fun n ↦ (K n).homology i) hsame
  apply isModuleComplete_extension R f (complexTowerMilnorSequence R K t i)
    (complexTowerMilnorSequence_shortExact R K t i)
  · exact isModuleComplete_coker R f (M := ModuleCat.of R (∀ n, (K n).homology (i - 1)))
      (N := ModuleCat.of R (∀ n, (K n).homology (i - 1)))
      (complexTowerHomologyDifference R K t (i - 1)) hp hp
  · exact isModuleComplete_ker R f (M := ModuleCat.of R (∀ n, (K n).homology i))
      (N := ModuleCat.of R (∀ n, (K n).homology i)) (complexTowerHomologyDifference R K t i) hs hs

/-- Koszul完備化候補の全次数のホモロジー加群は、各座標に関して導来完備。 -/
theorem koszulCompletionComplex_homology_isModuleComplete {e : ℕ}
    (a : Fin e → R) (j : Fin e) (i : ℤ) :
    IsModuleComplete R (a j) ((koszulCompletionComplex R a).homology i) :=
  complexTowerHomology_isModuleComplete_of_stages R (a j)
    (powerKoszulTower R a) (powerKoszulTransition R a) i
    (fun n ↦ powerKoszulStage_homology_isModuleComplete R a n j (i - 1))
    (fun n ↦ powerKoszulStage_homology_isModuleComplete R a n j i)

/-- 特にH⁰は、各座標に関して導来完備な加群。環構造は別工程。 -/
theorem koszulCompletionH0_isModuleComplete {e : ℕ} (a : Fin e → R) (j : Fin e) :
    IsModuleComplete R (a j) ((koszulCompletionComplex R a).homology 0) :=
  koszulCompletionComplex_homology_isModuleComplete R a j 0

end SerrePositivity.DerivedCompletion
