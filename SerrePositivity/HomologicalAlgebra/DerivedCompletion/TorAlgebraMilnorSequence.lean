module

public import SerrePositivity.HomologicalAlgebra.AlgebraEquivariantShortComplex
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorAlgebraMilnorMiddle
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorAlgebraMilnorActions

/-! # The original finite-test Milnor sequence as an actual coefficient-algebra sequence -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) [Module.Finite R M]
local notation "C₀" => ModuleCat.of R C
local notation "K₀" => finiteCoefficientTensorModel R C₀ M
local notation "S₀" => complexTowerMilnorSequence R (powerCokernelComplex a K₀)
  (powerCokernelComplexTransition a K₀)

/-- lim¹ Tor_(i+1) → Tor_i(C,M) → lim Tor_i, with actual C-linear maps. -/
def torAlgebraMilnorShortComplex (hC : IsModuleComplete R a C₀) (i : ℕ) :
    ShortComplex (ModuleCat.{u} C) := by
  let S := S₀ (-(i : ℤ))
  let X := modulePowerTorAlgebraLimOne a C M (i + 1)
  let Y := ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M
  let Z := modulePowerTorAlgebraLimit a C M i
  have hi : -(i : ℤ) - 1 = -((i + 1 : ℕ) : ℤ) := by omega
  let e₁ : S.X₁ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj X :=
    modulePowerCokernelTorAlgebraLimOneIsoAt a C M (-(i : ℤ) - 1) (i + 1) hi
  let e₂ : S.X₂ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj Y :=
    torAlgebraMilnorMiddleIso a C M hC i
  let e₃ : S.X₃ ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj Z :=
    (modulePowerCokernelTorAlgebraLimitComparison a C M i).toModuleIso
  let α : C → (S ⟶ S) := fun c => modulePowerCokernelMilnorScalarMap a C M c (-(i : ℤ))
  refine algebraEquivariantShortComplex S X Y Z e₁ e₂ e₃ α ?_ ?_ ?_
  · intro c
    exact modulePowerCokernelTorAlgebraLimOneIsoAt_scalar a C M (-(i : ℤ) - 1) (i + 1) hi c
  · intro c
    exact torAlgebraMilnorMiddleIso_scalar a C M hC i c
  · intro c
    ext x
    exact modulePowerCokernelTorAlgebraLimitComparison_scalar a C M i c x

/-- Forgetting coefficients recovers the original Milnor short complex and its original maps. -/
def torAlgebraMilnorShortComplex_restrictIso (hC : IsModuleComplete R a C₀) (i : ℕ) :
    S₀ (-(i : ℤ)) ≅ (torAlgebraMilnorShortComplex a C M hC i).map
      (ModuleCat.restrictScalars (algebraMap R C)) := by
  dsimp only [torAlgebraMilnorShortComplex]
  exact algebraEquivariantShortComplex_restrictIso _ _ _ _ _ _ _ _ _ _ _

lemma torAlgebraMilnorShortComplex_shortExact (hC : IsModuleComplete R a C₀) (i : ℕ) :
    (torAlgebraMilnorShortComplex a C M hC i).ShortExact := by
  dsimp only [torAlgebraMilnorShortComplex]
  apply algebraEquivariantShortComplex_shortExact
  exact complexTowerMilnorSequence_shortExact R _ _ (-(i : ℤ))

/-- The same sequence over an arbitrary original coefficient source B→C. -/
def torAlgebraMilnorShortComplexOver (hC : IsModuleComplete R a C₀) (i : ℕ)
    (B : Type u) [CommRing B] (ψ : B →+* C) : ShortComplex (ModuleCat.{u} B) :=
  (torAlgebraMilnorShortComplex a C M hC i).map (ModuleCat.restrictScalars ψ)

lemma torAlgebraMilnorShortComplexOver_shortExact (hC : IsModuleComplete R a C₀) (i : ℕ)
    (B : Type u) [CommRing B] (ψ : B →+* C) :
    (torAlgebraMilnorShortComplexOver a C M hC i B ψ).ShortExact :=
  (torAlgebraMilnorShortComplex_shortExact a C M hC i).map_of_exact (ModuleCat.restrictScalars ψ)

end SerrePositivity.DerivedCompletion
