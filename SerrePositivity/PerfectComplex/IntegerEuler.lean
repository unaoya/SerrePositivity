module
public import SerrePositivity.KTheory.HomologyEulerBasic
public import SerrePositivity.KTheory.G0.MaximalSupport
public import SerrePositivity.PerfectComplex.Free.Euler

/-! # Integer-valued Euler evaluation on complexes supported at a closed point -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits IsLocalRing
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

namespace K0WithSupport
/-- The integer Euler characteristic on the closed-point support. -/
def integerEuler : K0WithSupport (supportZeroLocus (maximalIdeal R)) →+ ℤ :=
  (maximalSupportLengthMap R).comp (homologyEuler (supportZeroLocus (maximalIdeal R)))

/-- Integer Euler evaluation is the finite alternating sum of homology lengths. -/
lemma integerEuler_mk (X : SupportedPerfectHomotopyOn (supportZeroLocus (maximalIdeal R))) :
    integerEuler R (mk _ X) = ∑ᶠ i : ℤ, ((i.negOnePow : ℤˣ) : ℤ) •
      ((Module.length R (supportedPerfectHomology _ X i).obj).toNat : ℤ) := by
  rw [integerEuler, AddMonoidHom.comp_apply, homologyEuler_mk]
  unfold supportedHomologyEuler supportedModuleEuler
  rw [(maximalSupportLengthMap R).map_finsum (supportedHomologyEuler_hasFiniteSupport _ X)]
  simp

section
variable {R}

/-- Compute Euler on any supported object represented by a concrete complex. -/
lemma integerEuler_mk_real_of_rep
    (X : SupportedPerfectHomotopyOn (supportZeroLocus (maximalIdeal R)))
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : X.obj.obj = (HomotopyCategory.quotient _ _).obj P) :
    (integerEuler R (mk _ X) : ℝ) = chiOrd P := by
  let Z := supportZeroLocus (maximalIdeal R)
  let L := (Int.castAddHom ℝ).comp (maximalSupportLengthMap R)
  have hlen (i : ℤ) : Module.length R (supportedPerfectHomology Z X i).obj =
      Module.length R (P.homology i) := by
    change Module.length R ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).obj
      X.obj.obj) = _
    rw [hP]
    exact ((HomotopyCategory.homologyFunctorFactors _ _ i).app P).toLinearEquiv.length_eq
  change L ((homologyEuler Z) (mk Z X)) = chiOrd P
  rw [homologyEuler_mk]
  unfold supportedHomologyEuler supportedModuleEuler
  rw [L.map_finsum (supportedHomologyEuler_hasFiniteSupport Z X)]
  unfold chiOrd
  congr 1
  funext i
  simp [L, hlen]
end

/-- Casting the integer Euler evaluation to the reals recovers the existing ordinary Euler value. -/
lemma integerEuler_mk_complex_real (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn (supportZeroLocus (maximalIdeal R)) P) :
    (integerEuler R (mk _ (supportedPerfectOnObj _ P hp hs)) : ℝ) = chiOrd P :=
  integerEuler_mk_real_of_rep _ P rfl
end K0WithSupport
end SerrePositivity
