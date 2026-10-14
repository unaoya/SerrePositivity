module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Closure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleResolution
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulStageComplete

/-! # Koszul逆系のホモトピー逆極限候補の導来完備性

局所化加群のK射影的分解を使って直積上の全次数の射を検出し、
差分の錐とシフトに関する閉性から候補対象の導来完備性を導く。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 各複体の導来像が完備なら、実際の複体の直積の導来像も完備。 -/
theorem isComplete_Q_product (f : R) (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ n, IsComplete R f (DerivedCategory.Q.obj (K n))) :
    IsComplete R f (DerivedCategory.Q.obj (piObj K)) := by
  intro m a
  let P := moduleResolutionComplex R (ModuleCat.of R (Localization.Away f))
  let e := moduleResolutionDerivedIso R (ModuleCat.of R (Localization.Away f))
  have hzero : e.hom ≫ a = 0 := by
    apply Q_shiftedHom_eq_zero_of_product_projections R P K m
    intro n
    rw [assoc, hK n m (a ≫ (DerivedCategory.Q.map (Pi.π K n))⟦m⟧'), comp_zero]
  apply (cancel_epi e.hom).mp
  simpa only [comp_zero] using hzero

/-- 各段が導来完備なら、差分の錐のモデルによるホモトピー逆極限候補も導来完備。 -/
theorem isComplete_complexTowerHomotopyLimitObject_of_stages (f : R)
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (hK : ∀ n, IsComplete R f (DerivedCategory.Q.obj (K n))) :
    IsComplete R f (complexTowerHomotopyLimitObject R K t) :=
  isComplete_complexTowerHomotopyLimitObject R f K t (isComplete_Q_product R f K hK)

/-- Koszul完備化候補の実導来対象は、指定された各座標に関して導来完備。 -/
theorem koszulCompletionObject_isComplete {e : ℕ} (a : Fin e → R) (j : Fin e) :
    IsComplete R (a j) (koszulCompletionObject R a) :=
  isComplete_complexTowerHomotopyLimitObject_of_stages R (a j)
    (powerKoszulTower R a) (powerKoszulTransition R a)
    (fun n ↦ powerKoszulStage_isComplete R a n j)

end SerrePositivity.DerivedCompletion
